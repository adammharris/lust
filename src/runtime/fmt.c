/* Implementation of the fmt API declared in fmt.h (W-STD-B). Included
   from fmt.h only in the runtime unit (LUST_IMPL). Each function names
   its Rust 1.99 counterpart; the write sequence follows Rust where a
   sink can see it (PadAdapter only sees newlines, so a run of text Rust
   writes in pieces may arrive here in one write). */

/* ---------- sinks ---------- */

static int lust_string_sink_write(lust_sink *k, const uint8_t *p, uint64_t n) {
    lust_string_push_bytes(k->direct, p, n);
    return 0;
}

void lust_sink_string(lust_sink *k, lust_String *s) {
    k->write = lust_string_sink_write;
    k->direct = s;
    k->write_char = NULL;
    k->keep_empty = 0;
}

void lust_user_sink_init(lust_user_sink *k, void *self, int (*write)(lust_sink *, const uint8_t *, uint64_t), int (*write_char)(lust_sink *, uint32_t)) {
    k->base.write = write;
    k->base.direct = NULL;
    k->base.write_char = write_char;
    k->base.keep_empty = 1;
    k->self = self;
}

/* The sinks of `print!` and `eprint!`: std formats straight into its
   locked Stdout (a LineWriter, panic.c `lust_print_out`) or its
   unbuffered Stderr, so each piece is written as it is formatted. */
static int lust_stdout_sink_write(lust_sink *k, const uint8_t *p, uint64_t n) {
    (void)k;
    lust_print_out(p, n);
    return 0;
}

static int lust_stderr_sink_write(lust_sink *k, const uint8_t *p, uint64_t n) {
    (void)k;
    fwrite(p, 1, n, stderr);
    fflush(stderr);
    return 0;
}

void lust_print_begin(lust_sink *k, int to_stderr) {
    flockfile(to_stderr ? stderr : stdout);
    k->write = to_stderr ? lust_stderr_sink_write : lust_stdout_sink_write;
    k->direct = NULL;
    k->write_char = NULL;
    k->keep_empty = 0;
}

void lust_print_end(int to_stderr) { funlockfile(to_stderr ? stderr : stdout); }

/* The `io::Write::write_fmt` sinks: stdout through the soft LineWriter
   (`lust_stdout_write_soft`, panic.c), stderr unbuffered with
   `write_all`'s retry on a short or interrupted write. The first
   failure's errno stays in `err`; later writes fail at once. */
static int lust_io_stdout_write(lust_sink *k, const uint8_t *p, uint64_t n) {
    lust_io_sink *io = (lust_io_sink *)k;
    if (io->err) return 1;
    io->err = lust_stdout_write_soft(p, n);
    return io->err != 0;
}

static int lust_io_stderr_write(lust_sink *k, const uint8_t *p, uint64_t n) {
    lust_io_sink *io = (lust_io_sink *)k;
    if (io->err) return 1;
    while (n) {
        size_t w = fwrite(p, 1, (size_t)n, stderr);
        if (!w) {
            int e = errno;
            clearerr(stderr);
            if (e == EINTR) continue;
            io->err = e ? e : EIO;
            return 1;
        }
        p += w;
        n -= w;
    }
    while (fflush(stderr) != 0) {
        int e = errno;
        clearerr(stderr);
        if (e == EINTR) continue;
        io->err = e ? e : EIO;
        return 1;
    }
    return 0;
}

void lust_io_begin(lust_io_sink *k, int to_stderr) {
    flockfile(to_stderr ? stderr : stdout);
    k->base.write = to_stderr ? lust_io_stderr_write : lust_io_stdout_write;
    k->base.direct = NULL;
    k->base.write_char = NULL;
    k->base.keep_empty = 0;
    k->err = 0;
}

/* PadAdapter::write_str: indent at each line start, over
   `s.split_inclusive('\n')`. */
static int lust_pad_sink_write(lust_sink *k, const uint8_t *p, uint64_t n) {
    lust_pad_sink *s = (lust_pad_sink *)k;
    uint64_t i = 0;
    while (i < n) {
        uint64_t j = i;
        while (j < n && p[j] != '\n') j++;
        if (j < n) j++;
        if (*s->on_newline && s->inner->write(s->inner, (const uint8_t *)"    ", 4)) return 1;
        *s->on_newline = p[j - 1] == '\n';
        if (s->inner->write(s->inner, p + i, j - i)) return 1;
        i = j;
    }
    return 0;
}

/* PadAdapter::write_char: the indent at a line start, then the char
   through the inner sink's own `write_char` (only a sink with one
   gets this callback). */
static int lust_pad_sink_write_char(lust_sink *k, uint32_t c) {
    lust_pad_sink *s = (lust_pad_sink *)k;
    if (*s->on_newline && s->inner->write(s->inner, (const uint8_t *)"    ", 4)) return 1;
    *s->on_newline = c == '\n';
    return s->inner->write_char(s->inner, c);
}

/* fmt::write: literal-only text is one write_str, also an empty one
   (a sink that keeps empty writes sees it, as a user writer does). */
int lust_args_write(const lust_Arguments *a, lust_sink *k) {
    if (a->fmt) return a->fmt(a->env, k);
    return a->len || k->keep_empty ? k->write(k, (const uint8_t *)a->text, a->len) : 0;
}

int lust_f_args(lust_Formatter *f, const lust_Arguments *a) {
    return lust_args_write(a, f->buf);
}

lust_String lust_args_to_string(const lust_Arguments *a) {
    lust_String s = lust_string_with_capacity(a->cap);
    lust_sink k;
    lust_sink_string(&k, &s);
    if (lust_args_write(a, &k)) lust_fmt_failed(0, 0);
    return s;
}

void lust_f_init(lust_Formatter *f, lust_sink *buf) {
    f->buf = buf;
    f->fill = ' ';
    f->align = LUST_ALIGN_UNKNOWN;
    f->flags = 0;
    f->width = 0;
    f->prec = 0;
}

void lust_f_set(lust_Formatter *f, uint32_t fill, uint32_t align, uint32_t flags, uint32_t width, uint32_t prec) {
    f->fill = fill;
    f->align = (uint8_t)align;
    f->flags = (uint8_t)flags;
    f->width = (flags & LUST_FLAG_WIDTH) ? (uint16_t)width : 0;
    f->prec = (flags & LUST_FLAG_PREC) ? (uint16_t)prec : 0;
}

/* Formatter::wrap_buf with a PadAdapter: the same options, writing
   through `s->pad` into `f`'s sink, sharing `state`. */
static lust_Formatter *lust_f_wrap_pad(lust_Formatter *f, lust_fmt_slot *s, uint8_t *state) {
    s->pad.base.write = lust_pad_sink_write;
    s->pad.base.direct = 0;
    s->pad.base.write_char = f->buf->write_char ? lust_pad_sink_write_char : NULL;
    s->pad.base.keep_empty = 0;
    s->pad.inner = f->buf;
    s->pad.on_newline = state;
    s->f = *f;
    s->f.buf = &s->pad.base;
    return &s->f;
}

int lust_f_write(lust_Formatter *f, const void *p, uint64_t n) {
    if (!n && !f->buf->keep_empty) return 0;
    return f->buf->write(f->buf, (const uint8_t *)p, n);
}

int lust_f_write_str(lust_Formatter *f, lust_str s) { return lust_f_write(f, s.ptr, s.len); }

static int lust_utf8_encode(uint32_t c, uint8_t *b) {
    if (c < 0x80) { b[0] = (uint8_t)c; return 1; }
    if (c < 0x800) { b[0] = 0xC0 | (c >> 6); b[1] = 0x80 | (c & 0x3F); return 2; }
    if (c < 0x10000) { b[0] = 0xE0 | (c >> 12); b[1] = 0x80 | ((c >> 6) & 0x3F); b[2] = 0x80 | (c & 0x3F); return 3; }
    b[0] = 0xF0 | (c >> 18); b[1] = 0x80 | ((c >> 12) & 0x3F); b[2] = 0x80 | ((c >> 6) & 0x3F); b[3] = 0x80 | (c & 0x3F);
    return 4;
}

int lust_utf8_char(uint32_t c, uint8_t *b) { return lust_utf8_encode(c, b); }

int lust_f_write_char(lust_Formatter *f, uint32_t c) {
    if (f->buf->write_char) return f->buf->write_char(f->buf, c);
    uint8_t b[4];
    int n = lust_utf8_encode(c, b);
    return f->buf->write(f->buf, b, (uint64_t)n);
}

static lust_str lust_cstr(const char *c) {
    lust_str s;
    s.ptr = (uint8_t *)c;
    s.len = strlen(c);
    return s;
}

/* `n` fill chars, one write_char each (PostPadding::write). */
static int lust_f_fill_n(lust_Formatter *f, uint32_t fill, uint32_t n) {
    for (uint32_t i = 0; i < n; i++) {
        if (lust_f_write_char(f, fill)) return 1;
    }
    return 0;
}

/* Formatter::padding: writes the pre-padding; *post gets the count the
   caller writes after the content (with the fill captured here). */
static int lust_f_padding(lust_Formatter *f, uint32_t padding, uint32_t dflt, uint32_t *post) {
    uint32_t align = f->align == LUST_ALIGN_UNKNOWN ? dflt : f->align;
    uint32_t left = align == LUST_ALIGN_LEFT ? 0 : align == LUST_ALIGN_RIGHT ? padding : padding / 2;
    if (lust_f_fill_n(f, f->fill, left)) return 1;
    *post = padding - left;
    return 0;
}

/* Formatter::pad. */
int lust_f_pad(lust_Formatter *f, lust_str s) {
    if (!(f->flags & (LUST_FLAG_WIDTH | LUST_FLAG_PREC))) return lust_f_write_str(f, s);
    uint64_t chars = 0;
    if (f->flags & LUST_FLAG_PREC) {
        uint64_t i = 0;
        while (chars < f->prec && i < s.len) {
            lust_utf8_next(s.ptr, &i);
            chars++;
        }
        s.len = i;
    } else {
        chars = lust_str_char_count(s);
    }
    if (chars < f->width) {
        uint32_t fill = f->fill, post = 0;
        if (lust_f_padding(f, (uint32_t)(f->width - chars), LUST_ALIGN_LEFT, &post)) return 1;
        if (lust_f_write_str(f, s)) return 1;
        return lust_f_fill_n(f, fill, post);
    }
    return lust_f_write_str(f, s);
}

/* pad_integral's write_prefix: the sign, then the prefix if asked. */
static int lust_f_write_prefix(lust_Formatter *f, uint32_t sign, int use_prefix, lust_str prefix) {
    if (sign && lust_f_write_char(f, sign)) return 1;
    if (use_prefix) return lust_f_write_str(f, prefix);
    return 0;
}

/* Formatter::pad_integral. `digits.len` counts bytes, as in Rust. On an
   error inside the zero-pad branch the options stay changed, as Rust's
   early `?` leaves them. */
int lust_f_pad_integral(lust_Formatter *f, int nonneg, lust_str prefix, lust_str digits) {
    uint64_t width = digits.len;
    uint32_t sign = 0;
    if (!nonneg) {
        sign = '-';
        width++;
    } else if (f->flags & LUST_FLAG_PLUS) {
        sign = '+';
        width++;
    }
    int use_prefix = (f->flags & LUST_FLAG_ALT) != 0;
    if (use_prefix) width += lust_str_char_count(prefix);
    uint64_t min = f->width;
    if (width >= min) {
        if (lust_f_write_prefix(f, sign, use_prefix, prefix)) return 1;
        return lust_f_write_str(f, digits);
    }
    uint32_t post = 0;
    if (f->flags & LUST_FLAG_ZERO) {
        uint32_t old_fill = f->fill;
        uint8_t old_align = f->align;
        f->fill = '0';
        f->align = LUST_ALIGN_RIGHT;
        if (lust_f_write_prefix(f, sign, use_prefix, prefix)) return 1;
        if (lust_f_padding(f, (uint32_t)(min - width), LUST_ALIGN_RIGHT, &post)) return 1;
        if (lust_f_write_str(f, digits)) return 1;
        if (lust_f_fill_n(f, '0', post)) return 1;
        f->fill = old_fill;
        f->align = old_align;
        return 0;
    }
    uint32_t fill = f->fill;
    if (lust_f_padding(f, (uint32_t)(min - width), LUST_ALIGN_RIGHT, &post)) return 1;
    if (lust_f_write_prefix(f, sign, use_prefix, prefix)) return 1;
    if (lust_f_write_str(f, digits)) return 1;
    return lust_f_fill_n(f, fill, post);
}

/* ---------- integers ---------- */

/* Decimal digits of a u128 into the tail of buf[40]; returns the start. */
static int lust_f_dec128(lust_u128 v, char *buf) {
    int i = 40;
    if (!v.lo && !v.hi) buf[--i] = '0';
    while (v.lo || v.hi) {
        uint64_t r;
        v = lust_u128_divmod64(v, 10, &r);
        buf[--i] = (char)('0' + r);
    }
    return i;
}

static int lust_f_dec_out(lust_Formatter *f, int nonneg, uint64_t lo, uint64_t hi) {
    char buf[40];
    lust_u128 v;
    v.lo = lo;
    v.hi = hi;
    int i = lust_f_dec128(v, buf);
    lust_str d;
    d.ptr = (uint8_t *)buf + i;
    d.len = (uint64_t)(40 - i);
    return lust_f_pad_integral(f, nonneg, lust_cstr(""), d);
}

int lust_f_u64(lust_Formatter *f, uint64_t v) { return lust_f_dec_out(f, 1, v, 0); }

int lust_f_i64(lust_Formatter *f, int64_t v) {
    uint64_t mag = v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
    return lust_f_dec_out(f, v >= 0, mag, 0);
}

int lust_f_u128(lust_Formatter *f, lust_u128 v) { return lust_f_dec_out(f, 1, v.lo, v.hi); }

int lust_f_i128(lust_Formatter *f, lust_i128 v) {
    int neg = (int64_t)v.hi < 0;
    lust_u128 m = neg ? lust_i128_mag(v) : lust_u128_from_i128(v);
    return lust_f_dec_out(f, !neg, m.lo, m.hi);
}

/* LowerHex, UpperHex, Octal, Binary (num.rs GenericRadix): the bits as
   unsigned, prefix 0x (also for X), 0o, 0b. */
int lust_f_radix(lust_Formatter *f, uint64_t lo, uint64_t hi, uint32_t mode) {
    static const char lower[] = "0123456789abcdef";
    static const char upper[] = "0123456789ABCDEF";
    const char *digs = mode == 2 ? upper : lower;
    uint64_t base = mode <= 2 ? 16 : mode == 3 ? 8 : 2;
    char buf[130];
    int i = 130;
    lust_u128 v;
    v.lo = lo;
    v.hi = hi;
    if (!v.lo && !v.hi) buf[--i] = '0';
    while (v.lo || v.hi) {
        uint64_t r;
        v = lust_u128_divmod64(v, base, &r);
        buf[--i] = digs[r];
    }
    lust_str d;
    d.ptr = (uint8_t *)buf + i;
    d.len = (uint64_t)(130 - i);
    return lust_f_pad_integral(f, 1, lust_cstr(mode <= 2 ? "0x" : mode == 3 ? "0o" : "0b"), d);
}

static int lust_f_debug_hex(const lust_Formatter *f) {
    return (f->flags & LUST_FLAG_DEBUG_LOWER_HEX) ? 1 : (f->flags & LUST_FLAG_DEBUG_UPPER_HEX) ? 2 : 0;
}

int lust_f_dbg_u64(lust_Formatter *f, uint64_t v) {
    int hex = lust_f_debug_hex(f);
    return hex ? lust_f_radix(f, v, 0, (uint32_t)hex) : lust_f_u64(f, v);
}

int lust_f_dbg_i64(lust_Formatter *f, int64_t v, uint64_t mask) {
    int hex = lust_f_debug_hex(f);
    return hex ? lust_f_radix(f, (uint64_t)v & mask, 0, (uint32_t)hex) : lust_f_i64(f, v);
}

int lust_f_dbg_u128(lust_Formatter *f, lust_u128 v) {
    int hex = lust_f_debug_hex(f);
    return hex ? lust_f_radix(f, v.lo, v.hi, (uint32_t)hex) : lust_f_u128(f, v);
}

int lust_f_dbg_i128(lust_Formatter *f, lust_i128 v) {
    int hex = lust_f_debug_hex(f);
    return hex ? lust_f_radix(f, v.lo, v.hi, (uint32_t)hex) : lust_f_i128(f, v);
}

/* ---------- floats, text leaves ---------- */

/* Runs `emit` style leaf output: append to the sink's String when it
   has one, else to a temporary that is then written in one piece. */
static lust_String *lust_f_out_begin(lust_Formatter *f, lust_String *tmp) {
    if (f->buf->direct) return f->buf->direct;
    *tmp = lust_string_new();
    return tmp;
}

static int lust_f_out_end(lust_Formatter *f, lust_String *out, lust_String *tmp) {
    if (out != tmp) return 0;
    int e = lust_f_write(f, tmp->ptr, tmp->len);
    lust_string_drop(tmp);
    return e;
}

static lust_float_spec lust_f_float_spec(const lust_Formatter *f, uint32_t mode) {
    lust_float_spec s;
    memset(&s, 0, sizeof s);
    s.precision = (f->flags & LUST_FLAG_PREC) ? f->prec : LUST_FLOAT_NO_PRECISION;
    s.mode = (uint8_t)mode;
    return s;
}

/* One numfmt::Part: `len` bytes copied from `p`, or `len` zeros when
   `p` is NULL (Part::Zero). Part::Num is a copy of its digits. */
typedef struct {
    const uint8_t *p;
    uint64_t len;
} lust_numpart;

/* Splits the magnitude text of float_core into the parts Rust's flt2dec
   builds for it (digits_to_dec_str and digits_to_exp_str), so each part
   is one write as in write_formatted_parts. `exact` is the fixed
   precision path, whose digit buffer keeps its trailing zeros. */
static int lust_float_split(const lust_String *core, int exact, lust_numpart *out) {
    const uint8_t *t = core->ptr;
    uint64_t n = core->len, i, e = n, dot = n;
    int k = 0;
    for (i = 0; i < n; i++) {
        if (t[i] == 'e' || t[i] == 'E') e = i;
        if (t[i] == '.' && dot == n) dot = i;
    }
    if (n >= 3 && (t[0] == 'N' || t[0] == 'i')) {
        out[k].p = t;
        out[k++].len = n;
        return k;
    }
    if (e < n) {
        /* Exponent form: [d][.][rest][e or e-][exp]; zero shortest is one
           copy ("0e0"), zero exact is [0.][zeros][e0]. */
        if (t[0] == '0' && (e == 1 || !exact)) {
            out[k].p = t;
            out[k++].len = n;
            return k;
        }
        if (t[0] == '0') {
            out[k].p = t;
            out[k++].len = 2;
            out[k].p = 0;
            out[k++].len = e - 2;
            out[k].p = t + e;
            out[k++].len = n - e;
            return k;
        }
        out[k].p = t;
        out[k++].len = 1;
        if (dot < e) {
            out[k].p = t + 1;
            out[k++].len = 1;
            out[k].p = t + 2;
            out[k++].len = e - 2;
        }
        uint64_t sign_len = (e + 1 < n && t[e + 1] == '-') ? 2 : 1;
        out[k].p = t + e;
        out[k++].len = sign_len;
        out[k].p = t + e + sign_len;
        out[k++].len = n - e - sign_len;
        return k;
    }
    if (n >= 2 && t[0] == '0' && t[1] == '.') {
        /* [0.][zeros][digits] */
        uint64_t z = 2;
        while (z < n && t[z] == '0') z++;
        out[k].p = t;
        out[k++].len = 2;
        out[k].p = 0;
        out[k++].len = z - 2;
        if (z < n) {
            out[k].p = t + z;
            out[k++].len = n - z;
        }
        return k;
    }
    int frac_zero = 1;
    for (i = dot + 1; i < n; i++)
        if (t[i] != '0') frac_zero = 0;
    if (exact || (dot < n && !frac_zero)) {
        /* [int][.][frac], or the whole digits when there is no point. */
        out[k].p = t;
        out[k++].len = dot;
        if (dot < n) {
            out[k].p = t + dot;
            out[k++].len = 1;
            out[k].p = t + dot + 1;
            out[k++].len = n - dot - 1;
        }
        return k;
    }
    /* Shortest digits ending before the point: [digits][zeros], then
       [.][zeros] for Debug's ".0". */
    uint64_t sig = dot;
    while (sig > 1 && t[sig - 1] == '0') sig--;
    out[k].p = t;
    out[k++].len = sig;
    out[k].p = 0;
    out[k++].len = dot - sig;
    if (dot < n) {
        out[k].p = t + dot;
        out[k++].len = 1;
        out[k].p = 0;
        out[k++].len = n - dot - 1;
    }
    return k;
}

/* Formatter::write_formatted_parts. */
static int lust_f_write_parts(lust_Formatter *f, const char *sign, const lust_numpart *parts, int k) {
    static const char zeros[] = "0000000000000000000000000000000000000000000000000000000000000000";
    if (sign[0] && lust_f_write(f, sign, 1)) return 1;
    for (int i = 0; i < k; i++) {
        if (parts[i].p) {
            if (lust_f_write(f, parts[i].p, parts[i].len)) return 1;
            continue;
        }
        uint64_t z = parts[i].len;
        while (z > 64) {
            if (lust_f_write(f, zeros, 64)) return 1;
            z -= 64;
        }
        if (z && lust_f_write(f, zeros, z)) return 1;
    }
    return 0;
}

/* float_to_*_common with Formatter::pad_formatted_parts. */
static int lust_f_float(lust_Formatter *f, const lust_fparts *p, uint32_t mode) {
    lust_float_spec spec = lust_f_float_spec(f, mode);
    lust_String core = lust_string_new();
    lust_numpart parts[8];
    lust_float_core(&core, p, spec);
    int k = lust_float_split(&core, spec.precision != LUST_FLOAT_NO_PRECISION, parts);
    const char *sign = p->special == 2 ? "" : p->sign ? "-" : (f->flags & LUST_FLAG_PLUS) ? "+" : "";
    int e;
    if (f->width == 0) {
        e = lust_f_write_parts(f, sign, parts, k);
    } else {
        uint32_t old_fill = f->fill;
        uint8_t old_align = f->align;
        uint64_t width = f->width;
        if (f->flags & LUST_FLAG_ZERO) {
            if (sign[0] && lust_f_write(f, sign, 1)) {
                lust_string_drop(&core);
                return 1;
            }
            width = width > (sign[0] ? 1u : 0u) ? width - (sign[0] ? 1u : 0u) : 0;
            sign = "";
            f->fill = '0';
            f->align = LUST_ALIGN_RIGHT;
        }
        uint64_t len = sign[0] ? 1 : 0;
        for (int i = 0; i < k; i++) len += parts[i].len;
        if (width <= len) {
            e = lust_f_write_parts(f, sign, parts, k);
        } else {
            uint32_t fill = f->fill, post = 0;
            e = lust_f_padding(f, (uint32_t)(width - len), LUST_ALIGN_RIGHT, &post) || lust_f_write_parts(f, sign, parts, k) ||
                lust_f_fill_n(f, fill, post);
        }
        f->fill = old_fill;
        f->align = old_align;
    }
    lust_string_drop(&core);
    return e;
}

int lust_f_f64(lust_Formatter *f, double v, uint32_t mode) {
    lust_fparts p = lust_f64_parts(v);
    return lust_f_float(f, &p, mode);
}

int lust_f_f32(lust_Formatter *f, float v, uint32_t mode) {
    lust_fparts p = lust_f32_parts(v);
    return lust_f_float(f, &p, mode);
}

/* bool Display (and Debug): str Display of "true" or "false". */
int lust_f_bool(lust_Formatter *f, uint8_t v) { return lust_f_pad(f, lust_cstr(v ? "true" : "false")); }

/* char Display: one write_char, or pad when a width or precision is set. */
int lust_f_char(lust_Formatter *f, uint32_t c) {
    if (!(f->flags & (LUST_FLAG_WIDTH | LUST_FLAG_PREC))) return lust_f_write_char(f, c);
    uint8_t b[4];
    lust_str s;
    s.ptr = b;
    s.len = (uint64_t)lust_utf8_encode(c, b);
    return lust_f_pad(f, s);
}

/* The escape text of one char for Debug (escape_debug_ext), in buf.
   Returns its byte length; `quote` is the quote char that escapes. */
static uint64_t lust_f_escape(uint32_t c, uint32_t quote, uint8_t *buf, uint64_t cap) {
    lust_String s = lust_string_new();
    lust_fmt_escape(&s, c, quote);
    uint64_t n = s.len < cap ? s.len : cap;
    memcpy(buf, s.ptr, n);
    lust_string_drop(&s);
    return n;
}

/* char Debug: quote, the escape, quote. No padding. An escape that is
   the char itself is one write_char (EscapeDebug's Display of its
   `Char` form), any other one write. */
int lust_f_dbg_char(lust_Formatter *f, uint32_t c) {
    uint8_t buf[16], one[4];
    uint64_t n = lust_f_escape(c, '\'', buf, sizeof buf);
    int one_n = lust_utf8_encode(c, one);
    int same = n == (uint64_t)one_n && memcmp(buf, one, n) == 0;
    return lust_f_write_char(f, '\'') || (same ? lust_f_write_char(f, c) : lust_f_write(f, buf, n)) || lust_f_write_char(f, '\'');
}

/* str Debug: runs of chars that need no escape are written whole,
   between the escapes, as in Rust's printable_range loop. */
int lust_f_dbg_str(lust_Formatter *f, lust_str s) {
    if (lust_f_write_char(f, '"')) return 1;
    uint64_t start = 0, i = 0;
    while (i < s.len) {
        uint8_t b = s.ptr[i];
        if (!(b > 0x7E || b < 0x20 || b == '\\' || b == '"')) {
            i++;
            continue;
        }
        uint64_t j = i;
        uint32_t c = lust_utf8_next(s.ptr, &j);
        uint8_t buf[16];
        uint64_t n = lust_f_escape(c, '"', buf, sizeof buf);
        uint8_t one[4];
        int one_n = lust_utf8_encode(c, one);
        if (n != (uint64_t)one_n || memcmp(buf, one, n) != 0) {
            lust_str run;
            run.ptr = s.ptr + start;
            run.len = i - start;
            if (lust_f_write_str(f, run) || lust_f_write(f, buf, n)) return 1;
            start = j;
        }
        i = j;
    }
    lust_str rest;
    rest.ptr = s.ptr + start;
    rest.len = s.len - start;
    return lust_f_write_str(f, rest) || lust_f_write_char(f, '"');
}

int lust_f_unit(lust_Formatter *f) { return lust_f_pad(f, lust_cstr("()")); }

/* fmt::Pointer (pointer_fmt_inner): the address as `{:#x}`; with `#`
   it is zero-padded, to 18 places when no width is set. */
int lust_f_pointer(lust_Formatter *f, const void *p) {
    lust_Formatter g = *f;
    if (g.flags & LUST_FLAG_ALT) {
        g.flags |= LUST_FLAG_ZERO;
        if (!(g.flags & LUST_FLAG_WIDTH)) {
            g.flags |= LUST_FLAG_WIDTH;
            g.width = 18;
        }
    }
    g.flags |= LUST_FLAG_ALT;
    return lust_f_radix(&g, (uint64_t)(uintptr_t)p, 0, 1);
}

/* A width or precision taken from a `usize` argument: Rust 1.99 keeps
   them in u16 and panics past it. */
uint32_t lust_f_count(uint64_t n, lust_loc loc) {
    if (n > 0xffffu) lust_panic_cstr("Formatting argument out of range", loc);
    return (uint32_t)n;
}

int lust_f_fnptr(lust_Formatter *f, const void *p) {
    lust_String tmp;
    lust_String *out = lust_f_out_begin(f, &tmp);
    lust_fmt_fnptr_debug(out, p);
    return lust_f_out_end(f, out, &tmp);
}

/* ---------- builders (builders.rs) ---------- */

static int lust_f_alt(const lust_Formatter *f) { return (f->flags & LUST_FLAG_ALT) != 0; }

/* panic=unwind: a field or entry fmt impl that panicked returns with its
   panic pending. Rust's unwinding leaves the builder there, so the
   builder fails: it writes nothing more (no `, `, `]`, or `}`). */
static int lust_f_unwinding(void) { return lust_unw_pending && lust_unw_mine(); }

void lust_dstruct_new(lust_DebugStruct *d, lust_Formatter *f, lust_str name) {
    d->fmt = f;
    d->err = (uint8_t)lust_f_write_str(f, name);
    d->has_fields = 0;
}

/* DebugStruct::field_with, up to the value. */
lust_Formatter *lust_dstruct_field(lust_DebugStruct *d, lust_fmt_slot *s, lust_str name) {
    lust_Formatter *w = 0;
    if (!d->err) {
        if (lust_f_alt(d->fmt)) {
            if (!d->has_fields && lust_f_write_str(d->fmt, lust_cstr(" {\n"))) goto fail;
            s->state = 1;
            w = lust_f_wrap_pad(d->fmt, s, &s->state);
        } else {
            if (lust_f_write_str(d->fmt, lust_cstr(d->has_fields ? ", " : " { "))) goto fail;
            w = d->fmt;
        }
        if (lust_f_write_str(w, name) || lust_f_write_str(w, lust_cstr(": "))) goto fail;
    }
    if (!w) d->has_fields = 1;
    return w;
fail:
    d->err = 1;
    d->has_fields = 1;
    return 0;
}

void lust_dstruct_field_end(lust_DebugStruct *d, lust_fmt_slot *s, int err) {
    if (err || lust_f_unwinding() || (lust_f_alt(d->fmt) && lust_f_write_str(&s->f, lust_cstr(",\n")))) d->err = 1;
    d->has_fields = 1;
}

int lust_dstruct_finish(lust_DebugStruct *d) {
    if (d->has_fields && !d->err) d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(lust_f_alt(d->fmt) ? "}" : " }"));
    return d->err;
}

int lust_dstruct_finish_ne(lust_DebugStruct *d) {
    if (d->err) return 1;
    if (d->has_fields) {
        if (lust_f_alt(d->fmt)) {
            lust_fmt_slot s;
            s.state = 1;
            lust_Formatter *w = lust_f_wrap_pad(d->fmt, &s, &s.state);
            d->err = (uint8_t)(lust_f_write_str(w, lust_cstr("..\n")) || lust_f_write_str(d->fmt, lust_cstr("}")));
        } else {
            d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(", .. }"));
        }
    } else {
        d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(" { .. }"));
    }
    return d->err;
}

void lust_dtuple_new(lust_DebugTuple *d, lust_Formatter *f, lust_str name) {
    d->fmt = f;
    d->err = (uint8_t)lust_f_write_str(f, name);
    d->fields = 0;
    d->empty_name = name.len == 0;
}

lust_Formatter *lust_dtuple_field(lust_DebugTuple *d, lust_fmt_slot *s) {
    lust_Formatter *w = 0;
    if (!d->err) {
        if (lust_f_alt(d->fmt)) {
            if (d->fields == 0 && lust_f_write_str(d->fmt, lust_cstr("(\n"))) goto fail;
            s->state = 1;
            w = lust_f_wrap_pad(d->fmt, s, &s->state);
        } else {
            if (lust_f_write_str(d->fmt, lust_cstr(d->fields == 0 ? "(" : ", "))) goto fail;
            w = d->fmt;
        }
    }
    if (!w) d->fields++;
    return w;
fail:
    d->err = 1;
    d->fields++;
    return 0;
}

void lust_dtuple_field_end(lust_DebugTuple *d, lust_fmt_slot *s, int err) {
    if (err || lust_f_unwinding() || (lust_f_alt(d->fmt) && lust_f_write_str(&s->f, lust_cstr(",\n")))) d->err = 1;
    d->fields++;
}

int lust_dtuple_finish(lust_DebugTuple *d) {
    if (d->fields > 0 && !d->err) {
        if (d->fields == 1 && d->empty_name && !lust_f_alt(d->fmt) && lust_f_write_str(d->fmt, lust_cstr(","))) {
            d->err = 1;
            return 1;
        }
        d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(")"));
    }
    return d->err;
}

int lust_dtuple_finish_ne(lust_DebugTuple *d) {
    if (d->err) return 1;
    if (d->fields > 0) {
        if (lust_f_alt(d->fmt)) {
            lust_fmt_slot s;
            s.state = 1;
            lust_Formatter *w = lust_f_wrap_pad(d->fmt, &s, &s.state);
            d->err = (uint8_t)(lust_f_write_str(w, lust_cstr("..\n")) || lust_f_write_str(d->fmt, lust_cstr(")")));
        } else {
            d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(", ..)"));
        }
    } else {
        d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr("(..)"));
    }
    return d->err;
}

void lust_dlist_new(lust_DebugList *d, lust_Formatter *f, int set) {
    d->fmt = f;
    d->set = (uint8_t)set;
    d->err = (uint8_t)lust_f_write_str(f, lust_cstr(set ? "{" : "["));
    d->has_fields = 0;
}

/* DebugInner::entry_with, up to the entry. */
lust_Formatter *lust_dlist_entry(lust_DebugList *d, lust_fmt_slot *s) {
    lust_Formatter *w = 0;
    if (!d->err) {
        if (lust_f_alt(d->fmt)) {
            if (!d->has_fields && lust_f_write_str(d->fmt, lust_cstr("\n"))) goto fail;
            s->state = 1;
            w = lust_f_wrap_pad(d->fmt, s, &s->state);
        } else {
            if (d->has_fields && lust_f_write_str(d->fmt, lust_cstr(", "))) goto fail;
            w = d->fmt;
        }
    }
    if (!w) d->has_fields = 1;
    return w;
fail:
    d->err = 1;
    d->has_fields = 1;
    return 0;
}

void lust_dlist_entry_end(lust_DebugList *d, lust_fmt_slot *s, int err) {
    if (err || lust_f_unwinding() || (lust_f_alt(d->fmt) && lust_f_write_str(&s->f, lust_cstr(",\n")))) d->err = 1;
    d->has_fields = 1;
}

int lust_dlist_finish(lust_DebugList *d) {
    if (!d->err) d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(d->set ? "}" : "]"));
    return d->err;
}

int lust_dlist_finish_ne(lust_DebugList *d) {
    if (d->err) return 1;
    const char *close = d->set ? "}" : "]";
    if (d->has_fields) {
        if (lust_f_alt(d->fmt)) {
            lust_fmt_slot s;
            s.state = 1;
            lust_Formatter *w = lust_f_wrap_pad(d->fmt, &s, &s.state);
            d->err = (uint8_t)(lust_f_write_str(w, lust_cstr("..\n")) || lust_f_write_str(d->fmt, lust_cstr(close)));
        } else {
            d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(d->set ? ", ..}" : ", ..]"));
        }
    } else {
        d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(d->set ? "..}" : "..]"));
    }
    return d->err;
}

void lust_dmap_new(lust_DebugMap *d, lust_Formatter *f) {
    d->fmt = f;
    d->err = (uint8_t)lust_f_write_str(f, lust_cstr("{"));
    d->has_fields = 0;
    d->has_key = 0;
    d->state = 1;
}

/* DebugMap's misuse panics come from core's builders.rs (no
   track_caller), as rustc 1.99 reports them; `loc` stays for the call
   shape. */
#define LUST_BUILDERS_RS "core/src/fmt/builders.rs:"

/* DebugMap::key_with, up to the key. */
lust_Formatter *lust_dmap_key(lust_DebugMap *d, lust_fmt_slot *s, lust_loc loc) {
    (void)loc;
    if (d->err) return 0;
    if (d->has_key) { lust_panic_std_lit("attempted to begin a new map entry without completing the previous one", LUST_BUILDERS_RS "1001:13"); return 0; }
    if (lust_f_alt(d->fmt)) {
        if (!d->has_fields && lust_f_write_str(d->fmt, lust_cstr("\n"))) goto fail;
        d->state = 1;
        return lust_f_wrap_pad(d->fmt, s, &d->state);
    }
    if (d->has_fields && lust_f_write_str(d->fmt, lust_cstr(", "))) goto fail;
    return d->fmt;
fail:
    d->err = 1;
    return 0;
}

void lust_dmap_key_end(lust_DebugMap *d, lust_fmt_slot *s, int err) {
    lust_Formatter *w = lust_f_alt(d->fmt) ? &s->f : d->fmt;
    if (err || lust_f_unwinding() || lust_f_write_str(w, lust_cstr(": "))) {
        d->err = 1;
        return;
    }
    d->has_key = 1;
}

/* DebugMap::value_with, up to the value. */
lust_Formatter *lust_dmap_value(lust_DebugMap *d, lust_fmt_slot *s, lust_loc loc) {
    (void)loc;
    if (d->err) {
        d->has_fields = 1;
        return 0;
    }
    if (!d->has_key) { lust_panic_std_lit("attempted to format a map value before its key", LUST_BUILDERS_RS "1077:13"); return 0; }
    if (lust_f_alt(d->fmt)) return lust_f_wrap_pad(d->fmt, s, &d->state);
    return d->fmt;
}

void lust_dmap_value_end(lust_DebugMap *d, lust_fmt_slot *s, int err) {
    if (err || lust_f_unwinding() || (lust_f_alt(d->fmt) && lust_f_write_str(&s->f, lust_cstr(",\n")))) {
        d->err = 1;
    } else {
        d->has_key = 0;
    }
    d->has_fields = 1;
}

int lust_dmap_finish(lust_DebugMap *d, lust_loc loc) {
    (void)loc;
    if (d->err) return 1;
    if (d->has_key) { lust_panic_std_lit("attempted to finish a map with a partial entry", LUST_BUILDERS_RS "1229:13"); return 0; }
    d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr("}"));
    return d->err;
}

int lust_dmap_finish_ne(lust_DebugMap *d, lust_loc loc) {
    (void)loc;
    if (d->err) return 1;
    if (d->has_key) { lust_panic_std_lit("attempted to finish a map with a partial entry", LUST_BUILDERS_RS "1180:13"); return 0; }
    if (d->has_fields) {
        if (lust_f_alt(d->fmt)) {
            lust_fmt_slot s;
            s.state = 1;
            lust_Formatter *w = lust_f_wrap_pad(d->fmt, &s, &s.state);
            d->err = (uint8_t)(lust_f_write_str(w, lust_cstr("..\n")) || lust_f_write_str(d->fmt, lust_cstr("}")));
        } else {
            d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr(", ..}"));
        }
    } else {
        d->err = (uint8_t)lust_f_write_str(d->fmt, lust_cstr("..}"));
    }
    return d->err;
}

void lust_fmt_failed(uint32_t what, lust_loc loc) {
    (void)loc;
    /* Rust raises these inside std, so they report std's location. */
    if (what == 1) lust_panic_std("a Display implementation returned an error unexpectedly: Error", "alloc/src/string.rs:2953:14");
    else if (what == 0) lust_panic_std("a formatting trait implementation returned an error when the underlying stream did not: Error", "alloc/src/fmt.rs:657:14");
    else lust_panic_std_lit("a formatting trait implementation returned an error when the underlying stream did not", "core/src/io/write.rs:411:17");
}
