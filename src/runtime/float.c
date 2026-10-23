/* Implementation of the float text API declared in float.h. Included from
   float.h only in the runtime unit (LUST_IMPL), so this text never reaches
   the per-unit declarations.

   Method, in short. No conversion goes through host float arithmetic
   (one checked fast path in the parser is the only exception), so the
   output cannot depend on the C compiler:
   - Shortest printing is a Ryu port (see lust_ryu_d2d). Rust picks the
     closest candidate and rounds exact ties up; ECMAScript (ryu-js)
     rounds exact ties to an even last digit. Both facts were measured
     against rustc 1.99 and ryu-js 1.0.2 and are re-checked by
     tests/float/fuzz.sh on every run.
   - Fixed-precision output rounds the value's exact decimal digits,
     computed with a fixed-size bignum, ties to even, exactly like
     Rust's exact (Dragon) path.
   - Parsing scales the decimal input into an exact bignum ratio and
     rounds it once to the target type, ties to even. A fast path
     (Clinger) covers short inputs that one IEEE multiply or divide
     decides exactly. */

/* ---------- bit access ---------- */

static uint64_t lust_f64_bits(double v) {
    uint64_t b;
    memcpy(&b, &v, 8);
    return b;
}
static double lust_f64_from_bits(uint64_t b) {
    double v;
    memcpy(&v, &b, 8);
    return v;
}
static uint32_t lust_f32_bits(float v) {
    uint32_t b;
    memcpy(&b, &v, 4);
    return b;
}
static float lust_f32_from_bits(uint32_t b) {
    float v;
    memcpy(&v, &b, 4);
    return v;
}

/* Splits a finite float bit pattern into magnitude = m * 2^e with m > 0
   (or m == 0 for zero). `boundary` is set when the gap to the next float
   below is half the gap above (mantissa exactly a power of two, but not
   the smallest normal). */

typedef struct {
    int sign;
    int special; /* 0 finite, 1 inf, 2 NaN */
    uint64_t m;
    int e;
    int boundary;
    int mant_bits; /* 53 or 24 (counting the hidden bit) */
    uint64_t ieee_mant; /* raw fraction bits */
    uint32_t ieee_exp;  /* raw exponent field */
} lust_fparts;

static lust_fparts lust_f64_parts(double v) {
    lust_fparts p;
    uint64_t b = lust_f64_bits(v);
    int exp = (int)((b >> 52) & 0x7FF);
    uint64_t frac = b & (((uint64_t)1 << 52) - 1);
    p.sign = (int)(b >> 63);
    p.mant_bits = 53;
    p.ieee_mant = frac;
    p.ieee_exp = (uint32_t)exp;
    p.boundary = frac == 0 && exp > 1;
    if (exp == 0x7FF) {
        p.special = frac ? 2 : 1;
        p.m = 0;
        p.e = 0;
    } else if (exp == 0) {
        p.special = 0;
        p.m = frac;
        p.e = -1074;
    } else {
        p.special = 0;
        p.m = frac | ((uint64_t)1 << 52);
        p.e = exp - 1075;
    }
    return p;
}

static lust_fparts lust_f32_parts(float v) {
    lust_fparts p;
    uint32_t b = lust_f32_bits(v);
    int exp = (int)((b >> 23) & 0xFF);
    uint32_t frac = b & 0x7FFFFF;
    p.sign = (int)(b >> 31);
    p.mant_bits = 24;
    p.ieee_mant = frac;
    p.ieee_exp = (uint32_t)exp;
    p.boundary = frac == 0 && exp > 1;
    if (exp == 0xFF) {
        p.special = frac ? 2 : 1;
        p.m = 0;
        p.e = 0;
    } else if (exp == 0) {
        p.special = 0;
        p.m = frac;
        p.e = -149;
    } else {
        p.special = 0;
        p.m = frac | (1u << 23);
        p.e = exp - 150;
    }
    return p;
}

/* ---------- fixed-size bignum ----------
   Little-endian base-2^32 limbs. 256 limbs (8192 bits) hold every value the
   parser and printer build: the largest is a 1024-digit decimal (3402 bits)
   next to 5^1400 (3250 bits), plus small shifts. No allocation, no state. */

#define LUST_BIG_MAX 256

typedef struct {
    uint32_t w[LUST_BIG_MAX];
    int n; /* limbs in use; 0 means zero */
} lust_big;

static void lust_big_zero(lust_big *a) { a->n = 0; }

static void lust_big_set_u64(lust_big *a, uint64_t v) {
    a->w[0] = (uint32_t)v;
    a->w[1] = (uint32_t)(v >> 32);
    a->n = (v >> 32) ? 2 : (v ? 1 : 0);
}

static void lust_big_norm(lust_big *a) {
    while (a->n > 0 && a->w[a->n - 1] == 0) a->n--;
}

static void lust_big_mul_small(lust_big *a, uint32_t m) {
    uint64_t carry = 0;
    int i;
    if (a->n == 0 || m == 1) return;
    if (m == 0) {
        a->n = 0;
        return;
    }
    for (i = 0; i < a->n; i++) {
        uint64_t t = (uint64_t)a->w[i] * m + carry;
        a->w[i] = (uint32_t)t;
        carry = t >> 32;
    }
    while (carry && a->n < LUST_BIG_MAX) {
        a->w[a->n++] = (uint32_t)carry;
        carry >>= 32;
    }
}

static void lust_big_add_small(lust_big *a, uint32_t v) {
    uint64_t carry = v;
    int i = 0;
    while (carry) {
        uint64_t t;
        if (i >= a->n) a->w[a->n++] = 0;
        t = (uint64_t)a->w[i] + carry;
        a->w[i] = (uint32_t)t;
        carry = t >> 32;
        i++;
    }
}

/* Multiplies by 5^k for k >= 0, in 5^13 steps (largest power that keeps
   limb products inside uint64 with carry to spare). */
static void lust_big_mul_pow5(lust_big *a, int k) {
    static const uint32_t pow5[] = {1, 5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125, 9765625, 48828125, 244140625};
    while (k >= 13) {
        lust_big_mul_small(a, 1220703125u);
        k -= 13;
    }
    if (k) lust_big_mul_small(a, pow5[k]);
}

/* Multiplies by 10^k for k >= 0, in 10^9 steps. */
static void lust_big_mul_pow10(lust_big *a, int k) {
    static const uint32_t pow10[] = {1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000};
    while (k >= 9) {
        lust_big_mul_small(a, 1000000000u);
        k -= 9;
    }
    if (k) lust_big_mul_small(a, pow10[k]);
}

/* *dst = *src << bits. dst and src may be the same bignum. */
static void lust_big_shl_to(lust_big *dst, const lust_big *src, int bits) {
    lust_big tmp;
    int limbs = bits / 32, rem = bits % 32, i;
    if (src->n == 0) {
        dst->n = 0;
        return;
    }
    tmp = *src;
    for (i = 0; i < tmp.n + limbs + 1 && i < LUST_BIG_MAX; i++) dst->w[i] = 0;
    for (i = 0; i < tmp.n; i++) {
        uint32_t lo = rem ? (tmp.w[i] << rem) : tmp.w[i];
        uint32_t hi = rem ? (tmp.w[i] >> (32 - rem)) : 0;
        dst->w[i + limbs] |= lo;
        if (hi) dst->w[i + limbs + 1] |= hi;
    }
    dst->n = tmp.n + limbs + 1;
    if (dst->n > LUST_BIG_MAX) dst->n = LUST_BIG_MAX;
    lust_big_norm(dst);
}

static void lust_big_shl(lust_big *a, int bits) {
    if (bits) lust_big_shl_to(a, a, bits);
}

static int lust_big_bitlen(const lust_big *a) {
    uint32_t top;
    int bits = 0;
    if (a->n == 0) return 0;
    top = a->w[a->n - 1];
    while (top) {
        bits++;
        top >>= 1;
    }
    return (a->n - 1) * 32 + bits;
}

static int lust_big_cmp(const lust_big *a, const lust_big *b) {
    int i;
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    for (i = a->n - 1; i >= 0; i--)
        if (a->w[i] != b->w[i]) return a->w[i] < b->w[i] ? -1 : 1;
    return 0;
}

/* *a -= *b. The caller guarantees *a >= *b. */
static void lust_big_sub(lust_big *a, const lust_big *b) {
    uint64_t borrow = 0;
    int i;
    for (i = 0; i < a->n; i++) {
        uint64_t sub = (i < b->n ? b->w[i] : 0) + borrow;
        uint64_t cur = a->w[i];
        a->w[i] = (uint32_t)(cur - sub);
        borrow = cur < sub ? 1 : 0;
    }
    lust_big_norm(a);
}

/* Divides by a small value in place, returns the remainder. */
static uint32_t lust_big_divmod_small(lust_big *a, uint32_t d) {
    uint64_t rem = 0;
    int i;
    for (i = a->n - 1; i >= 0; i--) {
        uint64_t cur = (rem << 32) | a->w[i];
        a->w[i] = (uint32_t)(cur / d);
        rem = cur % d;
    }
    lust_big_norm(a);
    return (uint32_t)rem;
}

/* *a >>= 1, in place. */
static void lust_big_shr1(lust_big *a) {
    int i;
    for (i = 0; i < a->n; i++) {
        uint32_t carry = (i + 1 < a->n ? (a->w[i + 1] & 1) : 0) << 31;
        a->w[i] = (a->w[i] >> 1) | carry;
    }
    lust_big_norm(a);
}

/* floor(a / b) for quotients of at most 64 bits, with *rem = a - q*b.
   Binary long division: shift the divisor up once, then walk it down.
   The parser only divides down to 54-bit quotients. */
static uint64_t lust_big_div_q64(const lust_big *a, const lust_big *b, lust_big *rem) {
    lust_big r = *a, d;
    uint64_t q = 0;
    int shift = lust_big_bitlen(a) - lust_big_bitlen(b);
    int i;
    if (shift < 0) {
        *rem = r;
        return 0;
    }
    lust_big_shl_to(&d, b, shift);
    for (i = shift; i >= 0; i--) {
        if (lust_big_cmp(&d, &r) <= 0) {
            lust_big_sub(&r, &d);
            q |= (uint64_t)1 << i;
        }
        lust_big_shr1(&d);
    }
    *rem = r;
    return q;
}

/* ---------- exact decimal digits ----------
   A positive value as (digits, len, e10) meaning 0.digits * 10^e10, with
   no leading or trailing zeros in digits. Every finite float has a finite
   exact form here: at most 767 significant digits for f64. */

#define LUST_DIG_MAX 800

typedef struct {
    char d[LUST_DIG_MAX];
    int len;
    int e10;
} lust_dec;

/* Exact digits of mant * 2^e2 for mant > 0. */
static void lust_dec_exact(lust_dec *out, uint64_t mant, int e2) {
    lust_big n;
    char rev[LUST_DIG_MAX];
    int rn = 0, off = 0, i;
    lust_big_set_u64(&n, mant);
    if (e2 >= 0) {
        lust_big_shl(&n, e2);
    } else {
        lust_big_mul_pow5(&n, -e2);
        off = e2; /* value = n * 10^off */
    }
    while (n.n > 0) {
        uint32_t chunk = lust_big_divmod_small(&n, 1000000000u);
        int c;
        if (n.n == 0) {
            while (chunk) {
                rev[rn++] = (char)('0' + chunk % 10);
                chunk /= 10;
            }
        } else {
            for (c = 0; c < 9; c++) {
                rev[rn++] = (char)('0' + chunk % 10);
                chunk /= 10;
            }
        }
    }
    out->len = rn;
    out->e10 = rn + off;
    for (i = 0; i < rn; i++) out->d[i] = rev[rn - 1 - i];
    while (out->len > 1 && out->d[out->len - 1] == '0') out->len--;
}

/* Compares two positive normalized decimals: -1, 0, or 1. The (d, len, e10)
   form allows a shorter `len` view of a longer digit string; trailing
   zeros past len read as zeros. */
static int lust_dec_cmp(const char *d1, int l1, int e1, const char *d2, int l2, int e2) {
    int i, n;
    if (e1 != e2) return e1 < e2 ? -1 : 1;
    n = l1 > l2 ? l1 : l2;
    for (i = 0; i < n; i++) {
        char a = i < l1 ? d1[i] : '0';
        char b = i < l2 ? d2[i] : '0';
        if (a != b) return a < b ? -1 : 1;
    }
    return 0;
}

/* ---------- shortest digits: Ryu ----------
   Ported from ryu-js 1.0.2 (d2s.rs, f2s.rs, the intrinsics files, and
   common.rs), itself a port of Ulf Adams' Ryu C code (Apache-2.0 or
   Boost-1.0). Two changes from the original:
   - 128-bit products use 32-bit limbs, because tcc has no __int128.
   - When tie_up is set, an exact tie between the two shortest
     candidates rounds up (Rust's rule) instead of to even (the
     ECMAScript rule). The tie is decided in exactly one place in
     each core loop, marked below.
   tests/float/fuzz.sh checks both tie modes against rustc and
   against the ryu-js crate itself. */

#include "ryu_tables.h"

static int lust_ryu_pow5bits(int e) { return (int)(((uint32_t)e * 1217359u) >> 19) + 1; }
static uint32_t lust_ryu_log10_pow2(int e) { return ((uint32_t)e * 78913u) >> 18; }
static uint32_t lust_ryu_log10_pow5(int e) { return ((uint32_t)e * 732923u) >> 20; }

/* High 64 bits of a*b; *lo_out gets the low 64 bits. */
static uint64_t lust_mul64_hi(uint64_t a, uint64_t b, uint64_t *lo_out) {
    uint64_t a0 = a & 0xFFFFFFFFu, a1 = a >> 32, b0 = b & 0xFFFFFFFFu, b1 = b >> 32;
    uint64_t p0 = a0 * b0, p1 = a0 * b1, p2 = a1 * b0, p3 = a1 * b1;
    uint64_t t = (p0 >> 32) + (p1 & 0xFFFFFFFFu) + (p2 & 0xFFFFFFFFu);
    *lo_out = (t << 32) | (p0 & 0xFFFFFFFFu);
    return p3 + (p1 >> 32) + (p2 >> 32) + (t >> 32);
}

/* ((m * mul) >> j) with mul a 128-bit table entry, as in Ryu: only the
   top 64 bits of the 192-bit product pair are formed. */
static uint64_t lust_ryu_mul_shift_64(uint64_t m, const uint64_t mul[2], uint32_t j) {
    uint64_t b2lo;
    uint64_t b0hi = lust_mul64_hi(m, mul[0], &b2lo);
    uint64_t b2hi = lust_mul64_hi(m, mul[1], &b2lo);
    uint64_t lo = b2lo + b0hi;
    uint64_t hi = b2hi + (lo < b2lo ? 1 : 0);
    int s = (int)j - 64;
    if (s <= 0) return lo << (0 - s);
    if (s >= 64) return s >= 128 ? 0 : hi >> (s - 64);
    return (lo >> s) | (hi << (64 - s));
}

static uint64_t lust_ryu_mul_shift_all_64(uint64_t m, const uint64_t mul[2], uint32_t j, uint64_t *vp, uint64_t *vm, uint32_t mm_shift) {
    *vp = lust_ryu_mul_shift_64(4 * m + 2, mul, j);
    *vm = lust_ryu_mul_shift_64(4 * m - 1 - mm_shift, mul, j);
    return lust_ryu_mul_shift_64(4 * m, mul, j);
}

static uint32_t lust_ryu_pow5_factor(uint64_t value) {
    const uint64_t m_inv_5 = 14757395258967641293ull;
    const uint64_t n_div_5 = 3689348814741910323ull;
    uint32_t count = 0;
    for (;;) {
        value *= m_inv_5;
        if (value > n_div_5) break;
        count++;
    }
    return count;
}
static int lust_ryu_multiple_of_pow5(uint64_t v, uint32_t p) { return lust_ryu_pow5_factor(v) >= p; }
static int lust_ryu_multiple_of_pow2(uint64_t v, uint32_t p) { return (v & (((uint64_t)1 << p) - 1)) == 0; }

typedef struct {
    uint64_t mant;
    int exp; /* value = mant * 10^exp */
} lust_ryu64;

static lust_ryu64 lust_ryu_d2d(uint64_t ieee_mant, uint32_t ieee_exp, int tie_up) {
    int e2;
    uint64_t m2;
    if (ieee_exp == 0) {
        e2 = 1 - 1023 - 52 - 2;
        m2 = ieee_mant;
    } else {
        e2 = (int)ieee_exp - 1023 - 52 - 2;
        m2 = ((uint64_t)1 << 52) | ieee_mant;
    }
    {
        int accept_bounds = (m2 & 1) == 0;
        uint64_t mv = 4 * m2;
        uint32_t mm_shift = (ieee_mant != 0 || ieee_exp <= 1) ? 1 : 0;
        uint64_t vr, vp, vm;
        int e10, vm_tz = 0, vr_tz = 0;
        if (e2 >= 0) {
            uint32_t q = lust_ryu_log10_pow2(e2) - (e2 > 3 ? 1 : 0);
            int k = 125 + lust_ryu_pow5bits((int)q) - 1;
            int i = -e2 + (int)q + k;
            e10 = (int)q;
            vr = lust_ryu_mul_shift_all_64(m2, lust_ryu_pow5_inv[q], (uint32_t)i, &vp, &vm, mm_shift);
            if (q <= 21) {
                uint64_t mv_mod5 = mv - (mv / 5) * 5;
                if (mv_mod5 == 0) {
                    vr_tz = lust_ryu_multiple_of_pow5(mv, q);
                } else if (accept_bounds) {
                    vm_tz = lust_ryu_multiple_of_pow5(mv - 1 - mm_shift, q);
                } else {
                    vp -= lust_ryu_multiple_of_pow5(mv + 2, q) ? 1 : 0;
                }
            }
        } else {
            uint32_t q = lust_ryu_log10_pow5(-e2) - (-e2 > 1 ? 1 : 0);
            int i = -e2 - (int)q;
            int k = lust_ryu_pow5bits(i) - 125;
            int j = (int)q - k;
            e10 = (int)q + e2;
            vr = lust_ryu_mul_shift_all_64(m2, lust_ryu_pow5[i], (uint32_t)j, &vp, &vm, mm_shift);
            if (q <= 1) {
                vr_tz = 1;
                if (accept_bounds)
                    vm_tz = mm_shift == 1;
                else
                    vp -= 1;
            } else if (q < 63) {
                vr_tz = lust_ryu_multiple_of_pow2(mv, q);
            }
        }
        {
            int removed = 0;
            uint8_t last_digit = 0;
            uint64_t output;
            if (vm_tz || vr_tz) {
                for (;;) {
                    uint64_t vp_d = vp / 10, vm_d = vm / 10;
                    uint64_t vr_d, vr_m;
                    if (vp_d <= vm_d) break;
                    vm_tz &= (vm - vm_d * 10) == 0;
                    vr_d = vr / 10;
                    vr_m = vr - vr_d * 10;
                    vr_tz &= last_digit == 0;
                    last_digit = (uint8_t)vr_m;
                    vr = vr_d;
                    vp = vp_d;
                    vm = vm_d;
                    removed++;
                }
                if (vm_tz) {
                    for (;;) {
                        uint64_t vm_d = vm / 10, vr_d, vr_m;
                        if ((vm - vm_d * 10) != 0) break;
                        vr_d = vr / 10;
                        vr_m = vr - vr_d * 10;
                        vr_tz &= last_digit == 0;
                        last_digit = (uint8_t)vr_m;
                        vr = vr_d;
                        vp /= 10;
                        vm = vm_d;
                        removed++;
                    }
                }
                /* The one tie rule: the exact value ends .....50..0.
                   ECMAScript keeps the even candidate; Rust rounds up. */
                if (!tie_up && vr_tz && last_digit == 5 && (vr & 1) == 0) last_digit = 4;
                output = vr + (((vr == vm && (!accept_bounds || !vm_tz)) || last_digit >= 5) ? 1 : 0);
            } else {
                int round_up = 0;
                uint64_t vp_d = vp / 100, vm_d = vm / 100;
                if (vp_d > vm_d) {
                    uint64_t vr_d = vr / 100;
                    round_up = (vr - vr_d * 100) >= 50;
                    vr = vr_d;
                    vp = vp_d;
                    vm = vm_d;
                    removed += 2;
                }
                for (;;) {
                    uint64_t vp10 = vp / 10, vm10 = vm / 10, vr_d;
                    if (vp10 <= vm10) break;
                    vr_d = vr / 10;
                    round_up = (vr - vr_d * 10) >= 5;
                    vr = vr_d;
                    vp = vp10;
                    vm = vm10;
                    removed++;
                }
                output = vr + ((vr == vm || round_up) ? 1 : 0);
            }
            {
                lust_ryu64 r;
                r.mant = output;
                r.exp = e10 + removed;
                return r;
            }
        }
    }
}

static uint32_t lust_ryu_mul_shift_32(uint32_t m, uint64_t factor, int shift) {
    uint64_t bits0 = (uint64_t)m * (uint32_t)factor;
    uint64_t bits1 = (uint64_t)m * (uint32_t)(factor >> 32);
    uint64_t sum = (bits0 >> 32) + bits1;
    return (uint32_t)(sum >> (shift - 32));
}
static uint32_t lust_ryu_mul_pow5_inv(uint32_t m, uint32_t q, int j) { return lust_ryu_mul_shift_32(m, lust_ryu_pow5_inv[q][1] + 1, j); }
static uint32_t lust_ryu_mul_pow5(uint32_t m, uint32_t i, int j) { return lust_ryu_mul_shift_32(m, lust_ryu_pow5[i][1], j); }
static int lust_ryu_multiple_of_pow5_32(uint32_t v, uint32_t p) {
    uint32_t count = 0;
    for (;;) {
        uint32_t q = v / 5;
        if (v - q * 5 != 0) break;
        v = q;
        count++;
    }
    return count >= p;
}
static int lust_ryu_multiple_of_pow2_32(uint32_t v, uint32_t p) { return (v & (((uint32_t)1 << p) - 1)) == 0; }

static lust_ryu64 lust_ryu_f2d(uint32_t ieee_mant, uint32_t ieee_exp, int tie_up) {
    int e2;
    uint32_t m2;
    if (ieee_exp == 0) {
        e2 = 1 - 127 - 23 - 2;
        m2 = ieee_mant;
    } else {
        e2 = (int)ieee_exp - 127 - 23 - 2;
        m2 = (1u << 23) | ieee_mant;
    }
    {
        int accept_bounds = (m2 & 1) == 0;
        uint32_t mv = 4 * m2, mp = 4 * m2 + 2;
        uint32_t mm_shift = (ieee_mant != 0 || ieee_exp <= 1) ? 1 : 0;
        uint32_t mm = 4 * m2 - 1 - mm_shift;
        uint32_t vr, vp, vm;
        int e10, vm_tz = 0, vr_tz = 0;
        uint8_t last_digit = 0;
        if (e2 >= 0) {
            uint32_t q = lust_ryu_log10_pow2(e2);
            int k = (125 - 64) + lust_ryu_pow5bits((int)q) - 1;
            int i = -e2 + (int)q + k;
            e10 = (int)q;
            vr = lust_ryu_mul_pow5_inv(mv, q, i);
            vp = lust_ryu_mul_pow5_inv(mp, q, i);
            vm = lust_ryu_mul_pow5_inv(mm, q, i);
            if (q != 0 && (vp - 1) / 10 <= vm / 10) {
                int l = (125 - 64) + lust_ryu_pow5bits((int)q - 1) - 1;
                last_digit = (uint8_t)(lust_ryu_mul_pow5_inv(mv, q - 1, -e2 + (int)q - 1 + l) % 10);
            }
            if (q <= 9) {
                if (mv % 5 == 0)
                    vr_tz = lust_ryu_multiple_of_pow5_32(mv, q);
                else if (accept_bounds)
                    vm_tz = lust_ryu_multiple_of_pow5_32(mm, q);
                else
                    vp -= lust_ryu_multiple_of_pow5_32(mp, q) ? 1 : 0;
            }
        } else {
            uint32_t q = lust_ryu_log10_pow5(-e2);
            int i = -e2 - (int)q;
            int k = lust_ryu_pow5bits(i) - (125 - 64);
            int j = (int)q - k;
            e10 = (int)q + e2;
            vr = lust_ryu_mul_pow5(mv, (uint32_t)i, j);
            vp = lust_ryu_mul_pow5(mp, (uint32_t)i, j);
            vm = lust_ryu_mul_pow5(mm, (uint32_t)i, j);
            if (q != 0 && (vp - 1) / 10 <= vm / 10) {
                j = (int)q - 1 - (lust_ryu_pow5bits(i + 1) - (125 - 64));
                last_digit = (uint8_t)(lust_ryu_mul_pow5(mv, (uint32_t)(i + 1), j) % 10);
            }
            if (q <= 1) {
                vr_tz = 1;
                if (accept_bounds)
                    vm_tz = mm_shift == 1;
                else
                    vp -= 1;
            } else if (q < 31) {
                vr_tz = lust_ryu_multiple_of_pow2_32(mv, q - 1);
            }
        }
        {
            int removed = 0;
            uint32_t output;
            if (vm_tz || vr_tz) {
                while (vp / 10 > vm / 10) {
                    vm_tz &= (vm - (vm / 10) * 10) == 0;
                    vr_tz &= last_digit == 0;
                    last_digit = (uint8_t)(vr % 10);
                    vr /= 10;
                    vp /= 10;
                    vm /= 10;
                    removed++;
                }
                if (vm_tz) {
                    while (vm % 10 == 0) {
                        vr_tz &= last_digit == 0;
                        last_digit = (uint8_t)(vr % 10);
                        vr /= 10;
                        vp /= 10;
                        vm /= 10;
                        removed++;
                    }
                }
                if (!tie_up && vr_tz && last_digit == 5 && (vr & 1) == 0) last_digit = 4;
                output = vr + (((vr == vm && (!accept_bounds || !vm_tz)) || last_digit >= 5) ? 1 : 0);
            } else {
                while (vp / 10 > vm / 10) {
                    last_digit = (uint8_t)(vr % 10);
                    vr /= 10;
                    vp /= 10;
                    vm /= 10;
                    removed++;
                }
                output = vr + ((vr == vm || last_digit >= 5) ? 1 : 0);
            }
            {
                lust_ryu64 r;
                r.mant = output;
                r.exp = e10 + removed;
                return r;
            }
        }
    }
}

/* Shortest digits that parse back to the float the parts describe.
   tie_up != 0 for Rust's rule, 0 for ECMAScript. */
static void lust_dec_shortest(lust_dec *out, const lust_fparts *p, int tie_up) {
    lust_ryu64 r = p->mant_bits == 53 ? lust_ryu_d2d(p->ieee_mant, p->ieee_exp, tie_up)
                                      : lust_ryu_f2d((uint32_t)p->ieee_mant, p->ieee_exp, tie_up);
    char rev[20];
    int n = 0, i;
    uint64_t mant = r.mant;
    do {
        rev[n++] = (char)('0' + mant % 10);
        mant /= 10;
    } while (mant);
    out->len = n;
    out->e10 = n + r.exp;
    for (i = 0; i < n; i++) out->d[i] = rev[n - 1 - i];
    while (out->len > 1 && out->d[out->len - 1] == '0') out->len--;
}

/* Digit at significant position i (0-based); '0' outside the stored digits.
   The exact and shortest forms drop trailing zeros, so this is how fixed
   renders reach positions past the last stored digit. */
static char lust_dec_digit(const lust_dec *v, int i) { return (i >= 0 && i < v->len) ? v->d[i] : '0'; }

/* Rounds the exact digits to `keep` significant digits (keep >= 1),
   round-half-to-even, exactly like Rust's fixed-precision path. */
static void lust_dec_round(lust_dec *v, int keep) {
    int i, up;
    if (v->len <= keep) return;
    up = 0;
    if (v->d[keep] > '5') {
        up = 1;
    } else if (v->d[keep] == '5') {
        int rest = 0;
        for (i = keep + 1; i < v->len; i++)
            if (v->d[i] != '0') rest = 1;
        up = rest || ((v->d[keep - 1] - '0') & 1);
    }
    v->len = keep;
    if (!up) return;
    i = keep - 1;
    while (i >= 0 && v->d[i] == '9') v->d[i--] = '0';
    if (i < 0) {
        v->d[0] = '1';
        v->len = 1;
        v->e10++;
    } else {
        v->d[i]++;
    }
}

/* ---------- magnitude renders (no sign; core is a scratch String) ---------- */

static void lust_push_zeros(lust_String *out, uint64_t n) {
    static const char zeros[] = "00000000000000000000000000000000";
    while (n >= 32) {
        lust_string_push_bytes(out, zeros, 32);
        n -= 32;
    }
    if (n) lust_string_push_bytes(out, zeros, n);
}

static void lust_push_int(lust_String *out, int v) {
    char b[16];
    int i = 16;
    unsigned mag = v < 0 ? 0u - (unsigned)v : (unsigned)v;
    if (v < 0) lust_string_push_bytes(out, "-", 1);
    do {
        b[--i] = (char)('0' + mag % 10);
        mag /= 10;
    } while (mag);
    lust_string_push_bytes(out, b + i, 16 - i);
}

/* Fixed layout from significant digits, fraction zeros trimmed.
   `debug` adds ".0" when the value has no fraction part. */
static void lust_render_fixed_shortest(lust_String *core, const lust_dec *v, int debug) {
    if (v->e10 <= 0) {
        lust_string_push_bytes(core, "0.", 2);
        lust_push_zeros(core, (uint64_t)(-v->e10));
        lust_string_push_bytes(core, v->d, v->len);
    } else if (v->e10 >= v->len) {
        lust_string_push_bytes(core, v->d, v->len);
        lust_push_zeros(core, (uint64_t)(v->e10 - v->len));
        if (debug) lust_string_push_bytes(core, ".0", 2);
    } else {
        lust_string_push_bytes(core, v->d, v->e10);
        lust_string_push_bytes(core, ".", 1);
        lust_string_push_bytes(core, v->d + v->e10, v->len - v->e10);
    }
}

/* Fixed layout with exactly `prec` fraction digits. The digits in *v must
   already be rounded so nothing past the kept positions is nonzero. */
static void lust_render_fixed_prec(lust_String *core, const lust_dec *v, uint32_t prec) {
    int i;
    uint32_t j;
    if (v->e10 > 0) {
        for (i = 0; i < v->e10; i++) {
            char c = lust_dec_digit(v, i);
            lust_string_push_bytes(core, &c, 1);
        }
    } else {
        lust_string_push_bytes(core, "0", 1);
    }
    if (prec == 0) return;
    lust_string_push_bytes(core, ".", 1);
    for (j = 1; j <= prec; j++) {
        char c = lust_dec_digit(v, v->e10 - 1 + (int)j);
        lust_string_push_bytes(core, &c, 1);
    }
}

/* Scientific layout. With precision, count = fraction digits wanted and
   the digits are pre-rounded; without, all shortest digits print. */
static void lust_render_exp(lust_String *core, const lust_dec *v, int upper, int precision, uint32_t prec) {
    char c = lust_dec_digit(v, 0);
    int i;
    lust_string_push_bytes(core, &c, 1);
    if (precision) {
        if (prec > 0) {
            uint32_t j;
            lust_string_push_bytes(core, ".", 1);
            for (j = 1; j <= prec; j++) {
                c = lust_dec_digit(v, (int)j);
                lust_string_push_bytes(core, &c, 1);
            }
        }
    } else if (v->len > 1) {
        lust_string_push_bytes(core, ".", 1);
        for (i = 1; i < v->len; i++) lust_string_push_bytes(core, v->d + i, 1);
    }
    c = upper ? 'E' : 'e';
    lust_string_push_bytes(core, &c, 1);
    lust_push_int(core, v->e10 - 1);
}

/* Builds the magnitude text (no sign, no padding) into core. */
static void lust_float_core(lust_String *core, const lust_fparts *p, lust_float_spec spec) {
    lust_dec v;
    int precision = spec.precision != LUST_FLOAT_NO_PRECISION;
    if (p->special == 2) {
        lust_string_push_cstr(core, "NaN");
        return;
    }
    if (p->special == 1) {
        lust_string_push_cstr(core, "inf");
        return;
    }
    if (p->m == 0) {
        v.d[0] = '0';
        v.len = 1;
        v.e10 = 1;
        if (spec.mode == LUST_FLOAT_LOWER_EXP || spec.mode == LUST_FLOAT_UPPER_EXP)
            lust_render_exp(core, &v, spec.mode == LUST_FLOAT_UPPER_EXP, precision, spec.precision);
        else if (precision)
            lust_render_fixed_prec(core, &v, spec.precision);
        else
            lust_string_push_cstr(core, spec.mode == LUST_FLOAT_DEBUG ? "0.0" : "0");
        return;
    }
    if (!precision) {
        lust_dec_shortest(&v, p, 1);
        if (spec.mode == LUST_FLOAT_LOWER_EXP || spec.mode == LUST_FLOAT_UPPER_EXP) {
            lust_render_exp(core, &v, spec.mode == LUST_FLOAT_UPPER_EXP, 0, 0);
        } else if (spec.mode == LUST_FLOAT_DEBUG && (v.e10 <= -4 || v.e10 >= 17)) {
            lust_render_exp(core, &v, 0, 0, 0);
        } else {
            lust_render_fixed_shortest(core, &v, spec.mode == LUST_FLOAT_DEBUG);
        }
        return;
    }
    lust_dec_exact(&v, p->m, p->e);
    if (spec.mode == LUST_FLOAT_LOWER_EXP || spec.mode == LUST_FLOAT_UPPER_EXP) {
        lust_dec_round(&v, (int)spec.precision + 1);
        lust_render_exp(core, &v, spec.mode == LUST_FLOAT_UPPER_EXP, 1, spec.precision);
        return;
    }
    {
        int keep = v.e10 + (int)spec.precision;
        if (keep < 0) {
            v.d[0] = '0';
            v.len = 1;
            v.e10 = 1;
        } else if (keep == 0) {
            /* Rounding to a whole unit in the last fraction place:
               the value sits below, at, or above half that unit. */
            int cmp = lust_dec_cmp(v.d, v.len, v.e10, "5", 1, v.e10);
            if (cmp <= 0) {
                v.d[0] = '0';
                v.len = 1;
                v.e10 = 1;
            } else {
                v.d[0] = '1';
                v.len = 1;
                v.e10 = v.e10 + 1;
            }
        } else {
            lust_dec_round(&v, keep);
        }
        lust_render_fixed_prec(core, &v, spec.precision);
    }
}

/* One float rendering with sign and padding, per Rust's Formatter rules. */
static void lust_float_format(lust_String *out, const lust_fparts *p, lust_float_spec spec) {
    lust_String core = lust_string_new();
    const char *sign = "";
    uint64_t sign_len, total, padn, i;
    uint32_t fill = spec.fill ? spec.fill : ' ';
    lust_float_core(&core, p, spec);
    if (p->special != 2) sign = p->sign ? "-" : (spec.plus ? "+" : "");
    sign_len = sign[0] ? 1 : 0;
    total = sign_len + core.len;
    if (spec.width <= total) {
        if (sign_len) lust_string_push_bytes(out, sign, 1);
        lust_string_push_str(out, lust_string_as_str(&core));
        free(core.ptr);
        return;
    }
    padn = spec.width - total;
    if (spec.zero_pad) {
        if (sign_len) lust_string_push_bytes(out, sign, 1);
        lust_push_zeros(out, padn);
        lust_string_push_str(out, lust_string_as_str(&core));
    } else if (spec.align == '<') {
        if (sign_len) lust_string_push_bytes(out, sign, 1);
        lust_string_push_str(out, lust_string_as_str(&core));
        for (i = 0; i < padn; i++) lust_string_push_char(out, fill);
    } else if (spec.align == '^') {
        uint64_t left = padn / 2;
        for (i = 0; i < left; i++) lust_string_push_char(out, fill);
        if (sign_len) lust_string_push_bytes(out, sign, 1);
        lust_string_push_str(out, lust_string_as_str(&core));
        for (i = left; i < padn; i++) lust_string_push_char(out, fill);
    } else {
        for (i = 0; i < padn; i++) lust_string_push_char(out, fill);
        if (sign_len) lust_string_push_bytes(out, sign, 1);
        lust_string_push_str(out, lust_string_as_str(&core));
    }
    free(core.ptr);
}

void lust_fmt_f64(lust_String *out, double v, lust_float_spec spec) {
    lust_fparts p = lust_f64_parts(v);
    lust_float_format(out, &p, spec);
}
void lust_fmt_f32(lust_String *out, float v, lust_float_spec spec) {
    lust_fparts p = lust_f32_parts(v);
    lust_float_format(out, &p, spec);
}

static lust_float_spec lust_spec_plain(uint8_t mode) {
    lust_float_spec s;
    memset(&s, 0, sizeof s);
    s.precision = LUST_FLOAT_NO_PRECISION;
    s.mode = mode;
    return s;
}
void lust_fmt_f64_display(lust_String *out, double v) { lust_fmt_f64(out, v, lust_spec_plain(LUST_FLOAT_DISPLAY)); }
void lust_fmt_f64_debug(lust_String *out, double v) { lust_fmt_f64(out, v, lust_spec_plain(LUST_FLOAT_DEBUG)); }
void lust_fmt_f32_display(lust_String *out, float v) { lust_fmt_f32(out, v, lust_spec_plain(LUST_FLOAT_DISPLAY)); }
void lust_fmt_f32_debug(lust_String *out, float v) { lust_fmt_f32(out, v, lust_spec_plain(LUST_FLOAT_DEBUG)); }

/* ---------- ECMAScript Number::toString (ryu-js Buffer::format) ---------- */

/* Writes the JS form into buf (at least 32 bytes), returns its length.
   Branch structure follows ryu-js 1.0.2 pretty/mod.rs: kk is the decimal
   point position (digits * 10^(kk-len)), fixed forms up to 21 digits,
   small fixed forms down to 1e-6, scientific otherwise with a signed
   exponent. */
static uint64_t lust_js_render(char *buf, const lust_fparts *p) {
    lust_dec v;
    int n = 0, i, kk, k, len;
    if (p->special == 2) {
        memcpy(buf, "NaN", 3);
        return 3;
    }
    if (p->special == 1) {
        if (p->sign) buf[n++] = '-';
        memcpy(buf + n, "Infinity", 8);
        return n + 8;
    }
    if (p->m == 0) {
        buf[0] = '0';
        return 1;
    }
    if (p->sign) buf[n++] = '-';
    lust_dec_shortest(&v, p, 0);
    kk = v.e10;
    len = v.len;
    k = kk - len;
    if (k >= 0 && kk <= 21) {
        memcpy(buf + n, v.d, len);
        n += len;
        for (i = 0; i < k; i++) buf[n++] = '0';
    } else if (kk > 0 && kk <= 21) {
        memcpy(buf + n, v.d, kk);
        n += kk;
        buf[n++] = '.';
        memcpy(buf + n, v.d + kk, len - kk);
        n += len - kk;
    } else if (kk > -6 && kk <= 0) {
        buf[n++] = '0';
        buf[n++] = '.';
        for (i = 0; i < -kk; i++) buf[n++] = '0';
        memcpy(buf + n, v.d, len);
        n += len;
    } else {
        int exp = kk - 1;
        buf[n++] = v.d[0];
        if (len > 1) {
            buf[n++] = '.';
            memcpy(buf + n, v.d + 1, len - 1);
            n += len - 1;
        }
        buf[n++] = 'e';
        buf[n++] = exp < 0 ? '-' : '+';
        if (exp < 0) exp = -exp;
        if (exp >= 100) buf[n++] = (char)('0' + exp / 100);
        if (exp >= 10) buf[n++] = (char)('0' + (exp / 10) % 10);
        buf[n++] = (char)('0' + exp % 10);
    }
    return (uint64_t)n;
}

uint64_t lust_fmt_js_f64_buf(char *buf, double v) {
    lust_fparts p = lust_f64_parts(v);
    return lust_js_render(buf, &p);
}
uint64_t lust_fmt_js_f32_buf(char *buf, float v) {
    lust_fparts p = lust_f32_parts(v);
    return lust_js_render(buf, &p);
}
void lust_fmt_js_f64(lust_String *out, double v) {
    char buf[40];
    lust_string_push_bytes(out, buf, lust_fmt_js_f64_buf(buf, v));
}
void lust_fmt_js_f32(lust_String *out, float v) {
    char buf[40];
    lust_string_push_bytes(out, buf, lust_fmt_js_f32_buf(buf, v));
}

/* ---------- parsing ---------- */

static int lust_lower_eq(const uint8_t *s, uint64_t n, const char *word) {
    uint64_t i;
    for (i = 0; word[i]; i++) {
        uint8_t c;
        if (i >= n) return 0;
        c = s[i];
        if (c >= 'A' && c <= 'Z') c = (uint8_t)(c + 32);
        if (c != (uint8_t)word[i]) return 0;
    }
    return i == n;
}

/* Exact powers of ten for the parser fast path. 10^k is exactly
   representable in f64 for k <= 22 and in f32 for k <= 10. */
static const double lust_pow10_d[23] = {1e0,  1e1,  1e2,  1e3,  1e4,  1e5,  1e6,  1e7,  1e8,  1e9,  1e10, 1e11,
                                        1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22};
static const float lust_pow10_f[11] = {1e0f, 1e1f, 1e2f, 1e3f, 1e4f, 1e5f, 1e6f, 1e7f, 1e8f, 1e9f, 1e10f};

/* Rounds the exact ratio (num / den) * 2^binexp to a float with `p`
   mantissa bits (hidden bit counted), exponent range [emin, emax] for
   normals, ties to even. `sticky` marks dropped nonzero input digits:
   the true value is a hair above the ratio, which can only matter at
   an exact tie (1024 kept digits is far past the 768 a tie can span).
   Returns the magnitude bit pattern (sign bit clear); inf on overflow. */
static uint64_t lust_ratio_to_float(const lust_big *num, const lust_big *den, int binexp, int sticky, int p, int emin, int emax) {
    lust_big a, b, rem, probe;
    int s, be, scale, shift;
    uint64_t q, mant;
    int up;
    /* be = floor(log2(value)): the bit-length difference brackets it
       to two choices; one comparison decides. */
    s = lust_big_bitlen(num) - lust_big_bitlen(den);
    if (s >= 0)
        lust_big_shl_to(&probe, den, s);
    else
        lust_big_shl_to(&probe, num, -s);
    /* ratio >= 2^s  <=>  (s>=0 ? num >= den<<s : num<<-s >= den) */
    be = s + binexp;
    if (s >= 0 ? lust_big_cmp(num, &probe) < 0 : lust_big_cmp(&probe, den) < 0) be--;
    /* Divide once at p+1 bits of output, then round the last bit. Below
       the normal range the output scale is fixed at the subnormal step. */
    scale = (be >= emin ? be : emin) - p;
    shift = binexp - scale;
    if (shift >= 0) {
        lust_big_shl_to(&a, num, shift);
        b = *den;
    } else {
        a = *num;
        lust_big_shl_to(&b, den, -shift);
    }
    q = lust_big_div_q64(&a, &b, &rem);
    mant = q >> 1;
    up = (q & 1) && (rem.n > 0 || sticky || (mant & 1));
    mant += up ? 1 : 0;
    if (be < emin) {
        /* Subnormal or zero; mant == 2^(p-1) is the smallest normal. */
        if (mant >= (uint64_t)1 << (p - 1)) return (uint64_t)1 << (p - 1);
        return mant;
    }
    if (mant >= (uint64_t)1 << p) {
        mant >>= 1;
        be++;
    }
    if (be > emax) return ((uint64_t)((1 << (p == 53 ? 11 : 8)) - 1)) << (p - 1);
    return ((uint64_t)(be - emin + 1) << (p - 1)) | (mant & (((uint64_t)1 << (p - 1)) - 1));
}

/* The grammar is Rust's: an optional sign, then inf / infinity / NaN
   (any case) or a decimal number, and nothing else. No whitespace, no
   underscores, no hex. On success returns the full bit pattern. */
#define LUST_PARSE_KEEP 1024

static int lust_parse_bits(lust_str s, int p, uint64_t *bits_out) {
    const uint8_t *b = s.ptr;
    uint64_t n = s.len, i = 0;
    int neg = 0, emin = p == 53 ? -1022 : -126, emax = p == 53 ? 1023 : 127;
    uint64_t sign_bit = p == 53 ? (uint64_t)1 << 63 : (uint64_t)1 << 31;
    uint64_t inf_bits = p == 53 ? (uint64_t)0x7FF << 52 : (uint64_t)0xFF << 23;
    uint64_t nan_bits = p == 53 ? ((uint64_t)0x7FF << 52) | ((uint64_t)1 << 51) : ((uint64_t)0xFF << 23) | ((uint64_t)1 << 22);
    uint64_t int_lo, int_hi, frac_lo, frac_hi, total, first_sig, kept, dropped, pos;
    int64_t exp_in = 0, dec_exp, e10;
    int sticky = 0;
    if (n == 0) return 1;
    if (b[i] == '+' || b[i] == '-') {
        neg = b[i] == '-';
        i++;
        if (i == n) return 2;
    }
    if (lust_lower_eq(b + i, n - i, "inf") || lust_lower_eq(b + i, n - i, "infinity")) {
        *bits_out = inf_bits | (neg ? sign_bit : 0);
        return 0;
    }
    if (lust_lower_eq(b + i, n - i, "nan")) {
        *bits_out = nan_bits | (neg ? sign_bit : 0);
        return 0;
    }
    int_lo = i;
    while (i < n && b[i] >= '0' && b[i] <= '9') i++;
    int_hi = i;
    frac_lo = frac_hi = i;
    if (i < n && b[i] == '.') {
        i++;
        frac_lo = i;
        while (i < n && b[i] >= '0' && b[i] <= '9') i++;
        frac_hi = i;
    }
    if (int_hi - int_lo + (frac_hi - frac_lo) == 0) return 2;
    if (i < n && (b[i] == 'e' || b[i] == 'E')) {
        int eneg = 0, any = 0;
        i++;
        if (i < n && (b[i] == '+' || b[i] == '-')) {
            eneg = b[i] == '-';
            i++;
        }
        while (i < n && b[i] >= '0' && b[i] <= '9') {
            any = 1;
            if (exp_in < (int64_t)1 << 40) exp_in = exp_in * 10 + (b[i] - '0');
            i++;
        }
        if (!any) return 2;
        if (eneg) exp_in = -exp_in;
    }
    if (i != n) return 2;
    /* Digit at concatenated position: int part then frac part. */
    total = int_hi - int_lo + (frac_hi - frac_lo);
    first_sig = 0;
    while (first_sig < total) {
        uint64_t q = first_sig < int_hi - int_lo ? int_lo + first_sig : frac_lo + (first_sig - (int_hi - int_lo));
        if (b[q] != '0') break;
        first_sig++;
    }
    if (first_sig == total) {
        *bits_out = neg ? sign_bit : 0;
        return 0;
    }
    kept = total - first_sig;
    if (kept > LUST_PARSE_KEEP) {
        dropped = kept - LUST_PARSE_KEEP;
        kept = LUST_PARSE_KEEP;
    } else {
        dropped = 0;
    }
    for (pos = first_sig + kept; pos < total; pos++) {
        uint64_t q = pos < int_hi - int_lo ? int_lo + pos : frac_lo + (pos - (int_hi - int_lo));
        if (b[q] != '0') sticky = 1;
    }
    e10 = exp_in - (int64_t)(frac_hi - frac_lo) + (int64_t)dropped;
    dec_exp = e10 + (int64_t)kept;
    {
        int64_t dec_hi = p == 53 ? 310 : 40;  /* value >= 10^(dec_hi-1) overflows */
        int64_t dec_lo = p == 53 ? -324 : -46; /* value < 10^dec_lo rounds to zero */
        if (dec_exp >= dec_hi) {
            *bits_out = inf_bits | (neg ? sign_bit : 0);
            return 0;
        }
        if (dec_exp <= dec_lo) {
            *bits_out = neg ? sign_bit : 0;
            return 0;
        }
    }
    /* Fast path: one exact operation decides the result. The bignum path
       below gives the same answer; this only saves time. */
    if (!dropped && kept <= 19) {
        uint64_t m = 0;
        for (pos = first_sig; pos < first_sig + kept; pos++) {
            uint64_t q = pos < int_hi - int_lo ? int_lo + pos : frac_lo + (pos - (int_hi - int_lo));
            m = m * 10 + (uint64_t)(b[q] - '0');
        }
        if (p == 53 && m <= (uint64_t)1 << 53 && e10 >= -22 && e10 <= 22) {
            double r = e10 >= 0 ? (double)m * lust_pow10_d[e10] : (double)m / lust_pow10_d[-e10];
            if (neg) r = -r;
            *bits_out = lust_f64_bits(r);
            return 0;
        }
        if (p == 24 && m <= (uint64_t)1 << 24 && e10 >= -10 && e10 <= 10) {
            float r = e10 >= 0 ? (float)m * lust_pow10_f[e10] : (float)m / lust_pow10_f[-e10];
            if (neg) r = -r;
            *bits_out = lust_f32_bits(r);
            return 0;
        }
    }
    {
        lust_big num, den;
        uint64_t mag;
        int e = (int)e10;
        lust_big_zero(&num);
        for (pos = first_sig; pos < first_sig + kept;) {
            uint32_t chunk = 0;
            int cnt = 0;
            while (pos < first_sig + kept && cnt < 9) {
                uint64_t q = pos < int_hi - int_lo ? int_lo + pos : frac_lo + (pos - (int_hi - int_lo));
                chunk = chunk * 10 + (uint32_t)(b[q] - '0');
                pos++;
                cnt++;
            }
            lust_big_mul_pow10(&num, cnt);
            lust_big_add_small(&num, chunk);
        }
        lust_big_set_u64(&den, 1);
        if (e >= 0) {
            lust_big_mul_pow5(&num, e);
        } else {
            lust_big_mul_pow5(&den, -e);
        }
        mag = lust_ratio_to_float(&num, &den, e, sticky, p, emin, emax);
        *bits_out = mag | (neg ? sign_bit : 0);
        return 0;
    }
}

int lust_parse_f64(lust_str s, double *out) {
    uint64_t bits;
    int rc = lust_parse_bits(s, 53, &bits);
    if (rc == 0) *out = lust_f64_from_bits(bits);
    return rc;
}
int lust_parse_f32(lust_str s, float *out) {
    uint64_t bits;
    int rc = lust_parse_bits(s, 24, &bits);
    if (rc == 0) *out = lust_f32_from_bits((uint32_t)bits);
    return rc;
}

/* ---------- casts ----------
   All done on the (m, e) integer form, so no host floating cast (with
   its undefined out-of-range behavior) is involved anywhere. */

typedef struct {
    uint64_t lo, hi;
} lust_u128w;

/* Truncated magnitude of the value as a 128-bit integer.
   Sets *overflow when it does not fit. */
static void lust_mag128(const lust_fparts *p, lust_u128w *out, int *overflow) {
    uint64_t m = p->m;
    int bl = 0;
    uint64_t t = m;
    out->lo = 0;
    out->hi = 0;
    *overflow = 0;
    if (m == 0) return;
    while (t) {
        bl++;
        t >>= 1;
    }
    if (p->e >= 0) {
        if (bl + p->e > 128) {
            *overflow = 1;
            return;
        }
        if (p->e >= 64) {
            out->hi = m << (p->e - 64);
        } else {
            out->lo = m << p->e;
            out->hi = p->e ? m >> (64 - p->e) : 0;
        }
    } else {
        int s = -p->e;
        out->lo = s >= 64 ? 0 : m >> s;
    }
}

static int lust_u128_gt(lust_u128w a, lust_u128w b) { return a.hi != b.hi ? a.hi > b.hi : a.lo > b.lo; }

/* The Rust `as` result for an int target of `bits` bits, as a 128-bit
   two's complement pattern (sign-extended past `bits`). */
static lust_u128w lust_cast_to_int(const lust_fparts *p, int bits, int is_signed) {
    lust_u128w mag, limit, out;
    int ovf;
    out.lo = 0;
    out.hi = 0;
    if (p->special == 2) return out; /* NaN -> 0 */
    if (p->special == 1) {
        ovf = 1;
        mag.lo = 0;
        mag.hi = 0;
    } else {
        lust_mag128(p, &mag, &ovf);
    }
    if (!is_signed && p->sign) return out; /* negative -> 0 */
    if (bits == 128) {
        if (is_signed) {
            limit.lo = 0;
            limit.hi = (uint64_t)1 << 63;
            if (!p->sign) limit.lo = ~(uint64_t)0, limit.hi = ((uint64_t)1 << 63) - 1;
        } else {
            limit.lo = ~(uint64_t)0;
            limit.hi = ~(uint64_t)0;
        }
    } else if (is_signed) {
        limit.hi = 0;
        limit.lo = p->sign ? (uint64_t)1 << (bits - 1) : (((uint64_t)1 << (bits - 1)) - 1);
        if (bits == 64 && !p->sign) limit.lo = 0x7FFFFFFFFFFFFFFFull;
    } else {
        limit.hi = 0;
        limit.lo = bits == 64 ? ~(uint64_t)0 : (((uint64_t)1 << bits) - 1);
    }
    if (ovf || lust_u128_gt(mag, limit)) mag = limit;
    if (is_signed && p->sign) {
        out.lo = ~mag.lo + 1;
        out.hi = ~mag.hi + (mag.lo == 0 ? 1 : 0);
    } else {
        out = mag;
    }
    return out;
}

#define LUST_F2I(FN, CT, PARTS, VAL, BITS, SIGNED)                                \
    CT FN(VAL v) {                                                                \
        lust_fparts p = PARTS(v);                                                 \
        lust_u128w r = lust_cast_to_int(&p, BITS, SIGNED);                        \
        return (CT)r.lo;                                                          \
    }
LUST_F2I(lust_f64_to_i8, int8_t, lust_f64_parts, double, 8, 1)
LUST_F2I(lust_f64_to_i16, int16_t, lust_f64_parts, double, 16, 1)
LUST_F2I(lust_f64_to_i32, int32_t, lust_f64_parts, double, 32, 1)
LUST_F2I(lust_f64_to_i64, int64_t, lust_f64_parts, double, 64, 1)
LUST_F2I(lust_f64_to_u8, uint8_t, lust_f64_parts, double, 8, 0)
LUST_F2I(lust_f64_to_u16, uint16_t, lust_f64_parts, double, 16, 0)
LUST_F2I(lust_f64_to_u32, uint32_t, lust_f64_parts, double, 32, 0)
LUST_F2I(lust_f64_to_u64, uint64_t, lust_f64_parts, double, 64, 0)
LUST_F2I(lust_f32_to_i8, int8_t, lust_f32_parts, float, 8, 1)
LUST_F2I(lust_f32_to_i16, int16_t, lust_f32_parts, float, 16, 1)
LUST_F2I(lust_f32_to_i32, int32_t, lust_f32_parts, float, 32, 1)
LUST_F2I(lust_f32_to_i64, int64_t, lust_f32_parts, float, 64, 1)
LUST_F2I(lust_f32_to_u8, uint8_t, lust_f32_parts, float, 8, 0)
LUST_F2I(lust_f32_to_u16, uint16_t, lust_f32_parts, float, 16, 0)
LUST_F2I(lust_f32_to_u32, uint32_t, lust_f32_parts, float, 32, 0)
LUST_F2I(lust_f32_to_u64, uint64_t, lust_f32_parts, float, 64, 0)
#undef LUST_F2I

void lust_f64_to_i128(double v, uint64_t *lo, uint64_t *hi) {
    lust_fparts p = lust_f64_parts(v);
    lust_u128w r = lust_cast_to_int(&p, 128, 1);
    *lo = r.lo;
    *hi = r.hi;
}
void lust_f64_to_u128(double v, uint64_t *lo, uint64_t *hi) {
    lust_fparts p = lust_f64_parts(v);
    lust_u128w r = lust_cast_to_int(&p, 128, 0);
    *lo = r.lo;
    *hi = r.hi;
}
void lust_f32_to_i128(float v, uint64_t *lo, uint64_t *hi) {
    lust_fparts p = lust_f32_parts(v);
    lust_u128w r = lust_cast_to_int(&p, 128, 1);
    *lo = r.lo;
    *hi = r.hi;
}
void lust_f32_to_u128(float v, uint64_t *lo, uint64_t *hi) {
    lust_fparts p = lust_f32_parts(v);
    lust_u128w r = lust_cast_to_int(&p, 128, 0);
    *lo = r.lo;
    *hi = r.hi;
}

/* Magnitude bits of an unsigned 128-bit integer rounded once to a float
   with p mantissa bits and exponent bias `bias`, ties to even. */
static uint64_t lust_u128_to_mag(uint64_t lo, uint64_t hi, int p, int bias) {
    int bl = 0, be, shift, i;
    uint64_t mant;
    if (hi) {
        uint64_t t = hi;
        bl = 64;
        while (t) {
            bl++;
            t >>= 1;
        }
    } else {
        uint64_t t = lo;
        while (t) {
            bl++;
            t >>= 1;
        }
    }
    if (bl == 0) return 0;
    be = bl - 1;
    if (bl <= p) {
        mant = lo << (p - bl);
    } else {
        int round_bit, sticky = 0;
        shift = bl - p;
        if (shift >= 64)
            mant = hi >> (shift - 64);
        else
            mant = (lo >> shift) | (shift ? hi << (64 - shift) : 0);
        /* bit (shift-1) is the round bit; anything below is sticky. */
        if (shift - 1 >= 64)
            round_bit = (int)((hi >> (shift - 65)) & 1);
        else
            round_bit = (int)((lo >> (shift - 1)) & 1);
        for (i = 0; i < shift - 1 && i < 64; i++)
            if ((lo >> i) & 1) sticky = 1;
        if (shift - 1 > 64) {
            if (lo) sticky = 1;
            for (i = 0; i < shift - 65; i++)
                if ((hi >> i) & 1) sticky = 1;
        }
        if (round_bit && (sticky || (mant & 1))) mant++;
        if (mant >> p) {
            mant >>= 1;
            be++;
        }
    }
    return ((uint64_t)(be + bias) << (p - 1)) | (mant & (((uint64_t)1 << (p - 1)) - 1));
}

double lust_i64_to_f64(int64_t v) {
    int sign = v < 0;
    uint64_t m = sign ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
    uint64_t bits = lust_u128_to_mag(m, 0, 53, 1023);
    return lust_f64_from_bits(bits | (sign ? (uint64_t)1 << 63 : 0));
}
double lust_u64_to_f64(uint64_t v) { return lust_f64_from_bits(lust_u128_to_mag(v, 0, 53, 1023)); }
float lust_i64_to_f32(int64_t v) {
    int sign = v < 0;
    uint64_t m = sign ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
    uint64_t bits = lust_u128_to_mag(m, 0, 24, 127);
    return lust_f32_from_bits((uint32_t)bits | (sign ? 1u << 31 : 0));
}
float lust_u64_to_f32(uint64_t v) { return lust_f32_from_bits((uint32_t)lust_u128_to_mag(v, 0, 24, 127)); }
double lust_u128_to_f64(uint64_t lo, uint64_t hi) { return lust_f64_from_bits(lust_u128_to_mag(lo, hi, 53, 1023)); }
float lust_u128_to_f32(uint64_t lo, uint64_t hi) { return lust_f32_from_bits((uint32_t)lust_u128_to_mag(lo, hi, 24, 127)); }
double lust_i128_to_f64(uint64_t lo, uint64_t hi) {
    int sign = (int)(hi >> 63);
    uint64_t bits;
    if (sign) {
        uint64_t nlo = ~lo + 1;
        uint64_t nhi = ~hi + (lo == 0 ? 1 : 0);
        bits = lust_u128_to_mag(nlo, nhi, 53, 1023);
    } else {
        bits = lust_u128_to_mag(lo, hi, 53, 1023);
    }
    return lust_f64_from_bits(bits | (sign ? (uint64_t)1 << 63 : 0));
}
float lust_i128_to_f32(uint64_t lo, uint64_t hi) {
    int sign = (int)(hi >> 63);
    uint64_t bits;
    if (sign) {
        uint64_t nlo = ~lo + 1;
        uint64_t nhi = ~hi + (lo == 0 ? 1 : 0);
        bits = lust_u128_to_mag(nlo, nhi, 24, 127);
    } else {
        bits = lust_u128_to_mag(lo, hi, 24, 127);
    }
    return lust_f32_from_bits((uint32_t)bits | (sign ? 1u << 31 : 0));
}

float lust_f64_to_f32(double v) {
    lust_fparts p = lust_f64_parts(v);
    uint64_t bits;
    if (p.special == 2) {
        uint64_t b = lust_f64_bits(v);
        uint32_t frac = (uint32_t)((b & (((uint64_t)1 << 52) - 1)) >> 29);
        if (!((b >> 51) & 1)) frac |= 1u << 22; /* signaling -> quiet */
        if (frac == 0) frac = 1u << 22;
        return lust_f32_from_bits((p.sign ? 1u << 31 : 0) | (0xFFu << 23) | frac);
    }
    if (p.special == 1) return lust_f32_from_bits((p.sign ? 1u << 31 : 0) | (0xFFu << 23));
    if (p.m == 0) return lust_f32_from_bits(p.sign ? 1u << 31 : 0);
    {
        lust_big num, den;
        lust_big_set_u64(&num, p.m);
        lust_big_set_u64(&den, 1);
        bits = lust_ratio_to_float(&num, &den, p.e, 0, 24, -126, 127);
    }
    return lust_f32_from_bits((uint32_t)bits | (p.sign ? 1u << 31 : 0));
}

double lust_f32_to_f64(float v) {
    lust_fparts p = lust_f32_parts(v);
    if (p.special == 2) {
        uint32_t b = lust_f32_bits(v);
        uint64_t frac = (uint64_t)(b & 0x7FFFFF) << 29;
        if (!((b >> 22) & 1)) frac |= (uint64_t)1 << 51; /* signaling -> quiet */
        return lust_f64_from_bits((p.sign ? (uint64_t)1 << 63 : 0) | ((uint64_t)0x7FF << 52) | frac);
    }
    if (p.special == 1) return lust_f64_from_bits((p.sign ? (uint64_t)1 << 63 : 0) | ((uint64_t)0x7FF << 52));
    if (p.m == 0) return lust_f64_from_bits(p.sign ? (uint64_t)1 << 63 : 0);
    {
        int bl = 0;
        uint64_t t = p.m, mant;
        while (t) {
            bl++;
            t >>= 1;
        }
        mant = p.m << (53 - bl);
        return lust_f64_from_bits((p.sign ? (uint64_t)1 << 63 : 0) | ((uint64_t)(bl - 1 + p.e + 1023) << 52) |
                                   (mant & (((uint64_t)1 << 52) - 1)));
    }
}


/* ---------- Float methods ---------- */

/* The libm entry points the float methods call. Rust lowers these
   methods to the same libm calls on this platform, so the results
   match bit for bit. Declarations live in float.h for all units;
   only the powi, min, max, and signum wrappers below are ours: their
   semantics are Rust-specific (reciprocal order, NaN choice, signed
   zeros), so a plain libm call would not match. */

double lust_f64_powi(double a, int32_t e) {
    uint32_t n = e < 0 ? (uint32_t)(-(int64_t)e) : (uint32_t)e;
    double r = 1.0, x = a;
    while (n) {
        if (n & 1) r *= x;
        n >>= 1;
        if (!n) break;
        x *= x;
    }
    return e < 0 ? 1.0 / r : r;
}
float lust_f32_powi(float a, int32_t e) {
    uint32_t n = e < 0 ? (uint32_t)(-(int64_t)e) : (uint32_t)e;
    float r = 1.0f, x = a;
    while (n) {
        if (n & 1) r *= x;
        n >>= 1;
        if (!n) break;
        x *= x;
    }
    return e < 0 ? 1.0f / r : r;
}

/* f64::min and f64::max: a NaN operand yields the other operand.
   Equal operands (0.0 and -0.0) are rustc's target's choice: on
   x86_64 the second one (so the zero sign of the second operand
   wins); on aarch64 fminnm and fmaxnm order -0.0 below 0.0, so min
   yields a -0.0 operand and max a 0.0 one (LUST_F_TIE). */
#if defined(__aarch64__)
#define LUST_F_TIE(a, b, want_neg) (lust_f_neg(a) == (want_neg) ? (a) : (b))
static int lust_f_neg(double x) { return x < 0 || (x == 0 && 1.0 / x < 0); }
#else
#define LUST_F_TIE(a, b, want_neg) (b)
#endif
double lust_f64_min(double a, double b) {
    if (a < b) return a;
    if (b < a) return b;
    if (a == b) return LUST_F_TIE(a, b, 1);
    return a == a ? a : b;
}
double lust_f64_max(double a, double b) {
    if (a > b) return a;
    if (b > a) return b;
    if (a == b) return LUST_F_TIE(a, b, 0);
    return a == a ? a : b;
}
float lust_f32_min(float a, float b) {
    if (a < b) return a;
    if (b < a) return b;
    if (a == b) return LUST_F_TIE(a, b, 1);
    return a == a ? a : b;
}
float lust_f32_max(float a, float b) {
    if (a > b) return a;
    if (b > a) return b;
    if (a == b) return LUST_F_TIE(a, b, 0);
    return a == a ? a : b;
}

double lust_f64_signum(double a) {
    if (a > 0) return 1.0;
    if (a < 0) return -1.0;
    if (a == 0) return lust_f64_bits(a) >> 63 ? -1.0 : 1.0;
    return a;
}
float lust_f32_signum(float a) {
    if (a > 0) return 1.0f;
    if (a < 0) return -1.0f;
    if (a == 0) return lust_f32_bits(a) >> 31 ? -1.0f : 1.0f;
    return a;
}

uint64_t lust_f64_to_bits(double v) { return lust_f64_bits(v); }
uint32_t lust_f32_to_bits(float v) { return lust_f32_bits(v); }
double lust_f64_from_bits_of(uint64_t b) { return lust_f64_from_bits(b); }
float lust_f32_from_bits_of(uint32_t b) { return lust_f32_from_bits(b); }
