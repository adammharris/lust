/* tcc predefines __STDC_VERSION__ as 199901L, so glibc hides the C11
   aligned_alloc declaration; without an explicit declaration tcc truncates
   its pointer return to int (spike K3-18). Declare both aligned entry
   points here. */
void *aligned_alloc(size_t alignment, size_t size);
int posix_memalign(void **memptr, size_t alignment, size_t size);

/* std's get_backtrace_style (panic.rs), read once per process: 1 Off
   (RUST_BACKTRACE unset or "0"), 2 Short (any other value), 3 Full
   ("full"). The default panic hook and the alloc error hook share it. */
#ifdef LUST_IMPL
static int32_t lust_bt_style_v;
#endif
int32_t lust_bt_style(void) LUST_BODY({
    int32_t s, zero = 0;
    __atomic_load(&lust_bt_style_v, &s, 0);
    if (s) return s;
    const char *e = getenv("RUST_BACKTRACE");
    s = !e || !strcmp(e, "0") ? 1 : !strcmp(e, "full") ? 3 : 2;
    if (!__atomic_compare_exchange(&lust_bt_style_v, &zero, &s, 0, 0, 0)) s = zero;
    return s;
})

/* The backtrace part of std's default hooks for `style`. lust has no
   frames, so Short and Full print only std's header (and Short its last
   note); difftest drops frame lines on both sides. Off prints the
   RUST_BACKTRACE note when `off_note` is set. */
void lust_bt_tail(int32_t style, int32_t off_note) LUST_BODY({
    if (style == 1 && off_note) fputs("note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace\n", stderr);
    else if (style == 2) fputs("stack backtrace:\nnote: Some details are omitted, run with `RUST_BACKTRACE=full` for a verbose backtrace.\n", stderr);
    else if (style == 3) fputs("stack backtrace:\n", stderr);
})

/* An allocation failure inside the runtime itself, where the size is not
   known. */
void lust_oom(void) LUST_BODY({
    fputs("memory allocation failed\n", stderr);
    lust_bt_tail(lust_bt_style(), 1);
    abort();
})

/* Rust's `capacity overflow` panic (RawVec, raw_vec/mod.rs:28:5): a requested byte size above
   isize::MAX, or a length sum that wraps usize. Defined before the
   String and Vec cores that call it. */
void lust_panic_std(const char *msg, const char *where); /* panic.c, included below */
void lust_panic_std_lit(const char *msg, const char *where);
void lust_vec_capacity_overflow(void) LUST_BODY({ lust_panic_std_lit("capacity overflow", "alloc/src/raw_vec/mod.rs:28:5"); })

/* std's rust_oom with the default alloc error hook (std/src/alloc.rs):
   `handle_alloc_error` for a layout of `n` bytes. The hook prints the
   RUST_BACKTRACE note on every call, not only the first. */
void lust_oom_size(uint64_t n) LUST_BODY({
    fprintf(stderr, "memory allocation of %llu bytes failed\n", (unsigned long long)n);
    lust_bt_tail(lust_bt_style(), 1);
    fflush(stderr);
    abort();
})

/* The `alloc(size, align)` intrinsic family (ARCH 3.2). `align` is a power
   of two, as Rust's Layout guarantees. Alignment up to 4 MiB works (the
   ts-rust jemalloc case). A zero size returns a dangling pointer with the
   requested alignment and allocates nothing; well-formed wrappers never
   ask for one, but the Vec core uses the same form for empty buffers.
   Every pointer these return can go to plain free(). */
void *lust_alloc(uint64_t size, uint64_t align) LUST_BODY({
    if (!size) return (void *)(uintptr_t)(align ? align : 1);
    void *p = 0;
#ifdef _WIN32
    p = align <= 16 ? malloc(size) : _aligned_malloc((size_t)size, (size_t)align);
#else
    if (align <= 16) p = malloc(size);
    else if ((size & (align - 1)) == 0) p = aligned_alloc(align, size);
    else if (posix_memalign(&p, align, size) != 0) p = 0;
#endif
    if (!p) lust_oom_size(size);
    return p;
})

/* std's System::alloc_zeroed: calloc when malloc's alignment is enough,
   so the pages stay untouched until used (`vec![0u8; n]` for a large n
   returns at once, as in Rust). */
void *lust_alloc_zeroed(uint64_t size, uint64_t align) LUST_BODY({
    if (!size) return (void *)(uintptr_t)(align ? align : 1);
    if (align <= 16) {
        void *p = calloc(size, 1);
        if (!p) lust_oom_size(size);
        return p;
    }
    void *p = lust_alloc(size, align);
    memset(p, 0, size);
    return p;
})

/* True when the `n` bytes at `p` are all zero. The `vec![x; n]` IsZero
   test for scalars and arrays of scalars (types without padding). */
int32_t lust_is_zeroed(const void *p, uint64_t n) LUST_BODY({
    const unsigned char *b = (const unsigned char *)p;
    for (uint64_t i = 0; i < n; i++) if (b[i]) return 0;
    return 1;
})

void lust_dealloc(void *ptr, uint64_t size, uint64_t align) LUST_BODY({
    if (!size) return;
#ifdef _WIN32
    if (align > 16) { _aligned_free(ptr); return; }
#endif
    (void)align;
    free(ptr);
})

/* An Rc/Arc count block's free (cgen `rc_head`): a unit that frees one may not know its
   value's size, and lust_dealloc reads no size but zero, which a count block never is. The
   same one call as lust_dealloc with the size. */
#define lust_rc_free(ptr, align) lust_dealloc((void *)(ptr), 1, (align))

/* realloc(ptr, old_size, align, new_size): the Rust GlobalAlloc argument
   order with Layout flattened. Always moves when the alignment exceeds
   what plain realloc promises; the copy is the smaller size. */
void *lust_realloc(void *ptr, uint64_t old_size, uint64_t align, uint64_t new_size) LUST_BODY({
    if (!new_size) {
        lust_dealloc(ptr, old_size, align);
        return (void *)(uintptr_t)(align ? align : 1);
    }
    if (!old_size) return lust_alloc(new_size, align);
    void *p = lust_alloc(new_size, align);
    memcpy(p, ptr, old_size < new_size ? old_size : new_size);
    lust_dealloc(ptr, old_size, align);
    return p;
})

/* Byte and raw-pointer intrinsics (ARCH 3.2). ptr_read and ptr_write are
   unaligned byte copies of `size` bytes: read is (dst, src, size), write
   is (dst, src, size), matching memcpy argument order. ptr_offset adds a
   signed byte offset carried in a usize. */
void lust_memcpy(void *dst, const void *src, uint64_t n) LUST_BODY({ memcpy(dst, src, n); })
void lust_memmove(void *dst, const void *src, uint64_t n) LUST_BODY({ memmove(dst, src, n); })
void lust_memset(void *dst, uint32_t byte, uint64_t n) LUST_BODY({ memset(dst, (int)byte, n); })
int32_t lust_memcmp(const void *a, const void *b, uint64_t n) LUST_BODY({ return memcmp(a, b, n); })
void lust_ptr_read(void *dst, const void *src, uint64_t size) LUST_BODY({ memcpy(dst, src, size); })
void lust_ptr_write(void *dst, const void *src, uint64_t size) LUST_BODY({ memcpy(dst, src, size); })
void *lust_ptr_offset(void *ptr, uint64_t offset) LUST_BODY({ return (char *)ptr + (int64_t)offset; })

/* ---------- Strings ---------- */

/* Empty buffers hold the dangling aligned pointer, never null, as in
   Rust: that is what makes the pointer-word niche of String and Vec
   valid (an empty value's pointer word is never a niche tag value). */
lust_String lust_string_new(void) LUST_BODY({ lust_String s = {(uint8_t *)(uintptr_t)1, 0, 0}; return s; })

/* String capacity follows the Vec<u8> RawVec rules below: minimum
   capacity 8, then max(cap * 2, len + extra) on the amortized path and
   exactly len + extra on the exact path. A len + extra sum that wraps
   usize, or a capacity above isize::MAX bytes, is a capacity overflow,
   as in the Vec core. */
void lust_string_reserve(lust_String *s, uint64_t extra) LUST_BODY({
    if (s->cap - s->len >= extra) return;
    uint64_t needed = s->len + extra;
    if (needed < s->len) { lust_vec_capacity_overflow(); return; }
    uint64_t cap = s->cap * 2;
    if (cap < needed) cap = needed;
    if (cap < 8) cap = 8;
    if (cap > (uint64_t)9223372036854775807ull) { lust_vec_capacity_overflow(); return; }
    s->ptr = lust_realloc(s->ptr, s->cap, 1, cap);
    s->cap = cap;
})

void lust_string_reserve_exact(lust_String *s, uint64_t extra) LUST_BODY({
    if (s->cap - s->len >= extra) return;
    uint64_t cap = s->len + extra;
    if (cap < s->len) { lust_vec_capacity_overflow(); return; }
    if (cap > (uint64_t)9223372036854775807ull) { lust_vec_capacity_overflow(); return; }
    s->ptr = lust_realloc(s->ptr, s->cap, 1, cap);
    s->cap = cap;
})

lust_String lust_string_with_capacity(uint64_t n) LUST_BODY({
    lust_String s = {(uint8_t *)(uintptr_t)1, 0, 0};
    if (n) {
        if (n > (uint64_t)9223372036854775807ull) { lust_vec_capacity_overflow(); return s; }
        s.ptr = lust_alloc(n, 1);
        s.cap = n;
    }
    return s;
})

void lust_string_push_bytes(lust_String *s, const void *p, uint64_t n) LUST_BODY({
    if (!n) return;
    lust_string_reserve(s, n);
    lust_copy_small(s->ptr + s->len, p, n);
    s->len += n;
})

void lust_string_push_str(lust_String *s, lust_str x) LUST_BODY({ lust_string_push_bytes(s, x.ptr, x.len); })

void lust_string_push_cstr(lust_String *s, const char *c) LUST_BODY({ lust_string_push_bytes(s, c, strlen(c)); })

void lust_string_push_char(lust_String *s, uint32_t c) LUST_BODY({
    uint8_t b[4];
    int n;
    if (c < 0x80) { b[0] = c; n = 1; }
    else if (c < 0x800) { b[0] = 0xC0 | (c >> 6); b[1] = 0x80 | (c & 0x3F); n = 2; }
    else if (c < 0x10000) { b[0] = 0xE0 | (c >> 12); b[1] = 0x80 | ((c >> 6) & 0x3F); b[2] = 0x80 | (c & 0x3F); n = 3; }
    else { b[0] = 0xF0 | (c >> 18); b[1] = 0x80 | ((c >> 12) & 0x3F); b[2] = 0x80 | ((c >> 6) & 0x3F); b[3] = 0x80 | (c & 0x3F); n = 4; }
    lust_string_push_bytes(s, b, n);
})

lust_String lust_string_from(lust_str x) LUST_BODY({
    lust_String s = lust_string_with_capacity(x.len);
    lust_string_push_str(&s, x);
    return s;
})

lust_str lust_string_as_str(lust_String *s) LUST_BODY({ lust_str r; r.ptr = s->ptr; r.len = s->len; return r; })
lust_String lust_string_clone(lust_String *s) LUST_BODY({ return lust_string_from(lust_string_as_str(s)); })
void lust_string_drop(lust_String *s) LUST_BODY({ lust_dealloc(s->ptr, s->cap, 1); })

int lust_str_cmp(lust_str a, lust_str b) LUST_BODY({
    uint64_t n = a.len < b.len ? a.len : b.len;
    int c = n ? memcmp(a.ptr, b.ptr, n) : 0;
    if (c) return c;
    return a.len < b.len ? -1 : a.len > b.len ? 1 : 0;
})
uint8_t lust_str_eq(lust_str a, lust_str b) LUST_BODY({ return a.len == b.len && (a.len == 0 || memcmp(a.ptr, b.ptr, a.len) == 0); })

#include "panic.c"
#include "thread.c"
#include "kconst.c"
/* ---------- Formatting ---------- */

void lust_fmt_u64(lust_String *out, uint64_t v) LUST_BODY({
    char b[24];
    int i = 24;
    do { b[--i] = '0' + v % 10; v /= 10; } while (v);
    lust_string_push_bytes(out, b + i, 24 - i);
})

void lust_fmt_i64(lust_String *out, int64_t v) LUST_BODY({
    if (v < 0) { lust_string_push_bytes(out, "-", 1); lust_fmt_u64(out, (uint64_t)0 - (uint64_t)v); }
    else lust_fmt_u64(out, (uint64_t)v);
})

void lust_fmt_bool(lust_String *out, uint8_t v) LUST_BODY({ lust_string_push_cstr(out, v ? "true" : "false"); })

#ifdef LUST_IMPL
#include "escape_table.h"
#include "unicode_table.h"

/* Binary search over one generated Unicode range table. */
static int lust_uni_in(const uint32_t ranges[][2], uint32_t n, uint32_t c) {
    uint32_t lo = 0, hi = n;
    while (lo < hi) {
        uint32_t mid = (lo + hi) / 2;
        if (c < ranges[mid][0]) hi = mid;
        else if (c > ranges[mid][1]) lo = mid + 1;
        else return 1;
    }
    return 0;
}
#define LUST_UNI_IN(table, c) lust_uni_in(table, (uint32_t)(sizeof table / sizeof table[0]), c)

/* True when Rust's escape_debug writes this scalar as \u{...}:
   binary search over the generated range table. */
static int lust_escape_unicode(uint32_t c) {
    return LUST_UNI_IN(lust_escape_ranges, c);
}
#endif

/* Debug text of a function pointer: `0x` and the address in lowercase
   hex with no leading zeroes, as Rust prints it. */
void lust_fmt_fnptr_debug(lust_String *out, const void *p) LUST_BODY({
    uint64_t v = (uint64_t)(uintptr_t)p;
    char buf[16];
    int n = 0;
    lust_string_push_cstr(out, "0x");
    if (!v) {
        lust_string_push_cstr(out, "0");
        return;
    }
    while (v) {
        buf[n++] = "0123456789abcdef"[v & 15];
        v >>= 4;
    }
    while (n) lust_string_push_char(out, (uint32_t)buf[--n]);
})

void lust_fmt_escape(lust_String *out, uint32_t c, uint32_t quote) LUST_BODY({
    switch (c) {
    case '\t': lust_string_push_cstr(out, "\\t"); return;
    case '\r': lust_string_push_cstr(out, "\\r"); return;
    case '\n': lust_string_push_cstr(out, "\\n"); return;
    case '\\': lust_string_push_cstr(out, "\\\\"); return;
    case 0: lust_string_push_cstr(out, "\\0"); return;
    }
    if (c == quote) { lust_string_push_bytes(out, "\\", 1); lust_string_push_char(out, c); return; }
    if (lust_escape_unicode(c)) {
        char b[16];
        snprintf(b, sizeof b, "\\u{%x}", c);
        lust_string_push_cstr(out, b);
        return;
    }
    lust_string_push_char(out, c);
})

/* Decodes one UTF-8 scalar. Input is valid UTF-8 (all lust strings are). */
uint32_t lust_utf8_next(const uint8_t *p, uint64_t *i) LUST_BODY({
    uint8_t b = p[*i];
    if (b < 0x80) { *i += 1; return b; }
    if (b < 0xE0) { uint32_t c = ((b & 0x1F) << 6) | (p[*i + 1] & 0x3F); *i += 2; return c; }
    if (b < 0xF0) { uint32_t c = ((b & 0x0F) << 12) | ((p[*i + 1] & 0x3F) << 6) | (p[*i + 2] & 0x3F); *i += 3; return c; }
    uint32_t c = ((b & 0x07) << 18) | ((p[*i + 1] & 0x3F) << 12) | ((p[*i + 2] & 0x3F) << 6) | (p[*i + 3] & 0x3F);
    *i += 4;
    return c;
})

void lust_fmt_str_debug(lust_String *out, lust_str s) LUST_BODY({
    lust_string_push_bytes(out, "\"", 1);
    uint64_t i = 0;
    while (i < s.len) lust_fmt_escape(out, lust_utf8_next(s.ptr, &i), '"');
    lust_string_push_bytes(out, "\"", 1);
})

void lust_fmt_char_debug(lust_String *out, uint32_t c) LUST_BODY({
    lust_string_push_bytes(out, "'", 1);
    lust_fmt_escape(out, c, '\'');
    lust_string_push_bytes(out, "'", 1);
})

/* Stdout goes through Rust's LineWriter model (panic.c); stderr is unbuffered. */
void lust_write(int to_stderr, lust_String *s) LUST_BODY({
    if (!to_stderr) lust_print_out(s->ptr, s->len);
    else if (s->len) { fwrite(s->ptr, 1, s->len, stderr); fflush(stderr); }
    lust_dealloc(s->ptr, s->cap, 1);
})

void lust_flush(void) LUST_BODY({ lust_print_flush(); })

/* The `exit` intrinsic behind std::process::exit: flush the held stdout
   tail, as Rust's rt::cleanup does. Destructors on the stack do not run,
   as in Rust; the calling thread's thread-local destructors do (glibc's
   exit() runs them for Rust std). */
void lust_exit(int32_t code) LUST_BODY({ lust_tls_exit(); lust_print_flush(); exit(code); })

/* ---------- Vec ---------- */

/* Erased Vec core (ARCH 3.3): capacity rules copy Rust 1.99 RawVec, so
   `capacity()` in the typed layer matches rustc byte for byte.
   - Minimum non-zero capacity: 8 elements when the element size is 1,
     4 when it is 2 to 1024, 1 above 1024.
   - Amortized reserve grows to max(cap * 2, len + extra, minimum).
   - Exact reserve and with_capacity take exactly the requested count.
   - A zero-sized element never allocates and stores capacity 0, as
     RawVec does: the stored word stays inside Cap's valid range
     0..=isize::MAX, so enum niches above it are free. The typed layer
     reports capacity UINT64_MAX (usize::MAX) for it (cgen vec_cap), and
     a reserve past usize::MAX elements is a capacity overflow.
   - A byte size above isize::MAX is a capacity overflow, as in Rust.
   The typed layer owns the shrink_to length assert; this core clamps
   the target at len, which is the same end state. */
void lust_vec_grow_to(lust_Vec *v, uint64_t new_cap, uint64_t elem, uint64_t align) LUST_BODY({
    if (!lust_vec_fits(new_cap, elem)) { lust_vec_capacity_overflow(); return; }
    v->ptr = lust_realloc(v->ptr, v->cap * elem, align, new_cap * elem);
    v->cap = new_cap;
})

void lust_vec_set_zst(lust_Vec *v, uint64_t align) LUST_BODY({
    v->ptr = (void *)(uintptr_t)(align ? align : 1);
    v->cap = 0;
})

void lust_vec_reserve(lust_Vec *v, uint64_t extra, uint64_t elem, uint64_t align) LUST_BODY({
    if (!elem) { lust_vec_set_zst(v, align); if (extra > 18446744073709551615ull - v->len) lust_vec_capacity_overflow(); return; }
    if (v->cap - v->len >= extra) return;
    uint64_t needed = v->len + extra;
    if (needed < v->len) { lust_vec_capacity_overflow(); return; }
    uint64_t cap = v->cap * 2;
    if (cap < needed) cap = needed;
    uint64_t min_cap = elem == 1 ? 8 : elem <= 1024 ? 4 : 1;
    if (cap < min_cap) cap = min_cap;
    lust_vec_grow_to(v, cap, elem, align);
})

void lust_vec_reserve_exact(lust_Vec *v, uint64_t extra, uint64_t elem, uint64_t align) LUST_BODY({
    if (!elem) { lust_vec_set_zst(v, align); if (extra > 18446744073709551615ull - v->len) lust_vec_capacity_overflow(); return; }
    if (v->cap - v->len >= extra) return;
    uint64_t needed = v->len + extra;
    if (needed < v->len) { lust_vec_capacity_overflow(); return; }
    lust_vec_grow_to(v, needed, elem, align);
})

lust_Vec lust_vec_with_capacity(uint64_t n, uint64_t elem, uint64_t align) LUST_BODY({
    lust_Vec v = {(void *)(uintptr_t)(align ? align : 1), 0, 0};
    if (!elem) { lust_vec_set_zst(&v, align); return v; }
    if (n) {
        if (!lust_vec_fits(n, elem)) { lust_vec_capacity_overflow(); return v; }
        v.ptr = lust_alloc(n * elem, align);
        v.cap = n;
    }
    return v;
})

/* RawVec::with_capacity_zeroed: `vec![x; n]` for a value whose bytes
   are all zero (Rust's IsZero fast path). The same capacity overflow
   rule as lust_vec_with_capacity; the memory comes from calloc. */
lust_Vec lust_vec_with_capacity_zeroed(uint64_t n, uint64_t elem, uint64_t align) LUST_BODY({
    lust_Vec v = {(void *)(uintptr_t)(align ? align : 1), 0, 0};
    if (!elem) { lust_vec_set_zst(&v, align); return v; }
    if (n) {
        if (!lust_vec_fits(n, elem)) { lust_vec_capacity_overflow(); return v; }
        v.ptr = lust_alloc_zeroed(n * elem, align);
        v.cap = n;
    }
    return v;
})

void lust_vec_shrink_to(lust_Vec *v, uint64_t min_cap, uint64_t elem, uint64_t align) LUST_BODY({
    if (!elem) return;
    uint64_t target = min_cap > v->len ? min_cap : v->len;
    if (v->cap <= target) return;
    if (!target) {
        free(v->ptr);
        v->ptr = (void *)(uintptr_t)(align ? align : 1);
        v->cap = 0;
        return;
    }
    v->ptr = lust_realloc(v->ptr, v->cap * elem, align, target * elem);
    v->cap = target;
})

void *lust_vec_push_slot(lust_Vec *v, uint64_t elem, uint64_t align) LUST_BODY({
    lust_vec_reserve(v, 1, elem, align);
    return (char *)v->ptr + (v->len++) * elem;
})

/* Panics with "<a><n><b><m><c>": the shape of Rust's index and range
   messages ("removal index (is 5) should be < len (is 3)"). */
void lust_panic_nn(const char *a, uint64_t n, const char *b, uint64_t m, const char *c, lust_loc loc) LUST_BODY({
    lust_String s = lust_string_new();
    lust_string_push_cstr(&s, a);
    lust_fmt_u64(&s, n);
    lust_string_push_cstr(&s, b);
    lust_fmt_u64(&s, m);
    lust_string_push_cstr(&s, c);
    lust_panic_dyn(&s, loc);
})

/* The end of a slice range, checked in Rust 1.99's order: the start
   against the length, the end against the length (an inclusive end
   prints as written; u64::MAX always fails), then start against end. */
uint64_t lust_slice_range(uint64_t lo, uint64_t hi, int inclusive, uint64_t len, lust_loc loc) LUST_BODY({
    if (lo > len) { lust_panic_nn("range start index ", lo, " out of range for slice of length ", len, "", loc); return lo; }
    if (inclusive ? hi >= len : hi > len) { lust_panic_nn("range end index ", hi, " out of range for slice of length ", len, "", loc); return lo; }
    uint64_t end = inclusive ? hi + 1 : hi;
    if (lo > end) { lust_panic_nn("slice index starts at ", lo, " but ends at ", end, "", loc); return lo; }
    return end;
})

#ifdef LUST_IMPL
/* Panics because byte `i` of `ptr` is not a char boundary: names the
   char it falls in, as Rust 1.99 does. */
static void lust_str_boundary_fail(const char *which, const uint8_t *ptr, uint64_t i, lust_loc loc) {
    uint64_t a = i;
    while (a > 0 && (ptr[a] & 0xC0) == 0x80) a--;
    uint64_t b = a;
    uint32_t c = lust_utf8_next(ptr, &b);
    lust_String s = lust_string_new();
    lust_string_push_cstr(&s, which);
    lust_fmt_u64(&s, i);
    lust_string_push_cstr(&s, " is not a char boundary; it is inside ");
    lust_fmt_char_debug(&s, c);
    lust_string_push_cstr(&s, " (bytes ");
    lust_fmt_u64(&s, a);
    lust_string_push_cstr(&s, "..");
    lust_fmt_u64(&s, b);
    lust_string_push_cstr(&s, " of string)");
    lust_panic_dyn(&s, loc);
}
#endif

/* The end of a str slice range, checked in Rust 1.99's order
   (`slice_error_fail_rt`): start and end against the length, start
   against end, then both on UTF-8 char boundaries (the end of the string
   or a byte that is not a continuation byte). An inclusive end at the
   length stays as written, so its boundary checks come first and its
   own out-of-bounds message last, as in core. */
uint64_t lust_str_range(const uint8_t *ptr, uint64_t lo, uint64_t hi, int inclusive, uint64_t len, lust_loc loc) LUST_BODY({
    if (lo > len) { lust_panic_nn("start byte index ", lo, " is out of bounds for string of length ", len, "", loc); return lo; }
    if (hi > len) { lust_panic_nn("end byte index ", hi, " is out of bounds for string of length ", len, "", loc); return lo; }
    uint64_t end = inclusive && hi < len ? hi + 1 : hi;
    if (lo > end) { lust_panic_nn("byte range starts at ", lo, " but ends at ", end, "", loc); return lo; }
    if (lo < len && (ptr[lo] & 0xC0) == 0x80) { lust_str_boundary_fail("start byte index ", ptr, lo, loc); return lo; }
    if (end < len && (ptr[end] & 0xC0) == 0x80) { lust_str_boundary_fail("end byte index ", ptr, end, loc); return lo; }
    if (inclusive && hi == len) { lust_panic_nn("end byte index ", hi, " is out of bounds for string of length ", len, "", loc); return lo; }
    return end;
})

/* A `lust_loc` for a line of std source (panic.c's `lust_std_files`
   index, line, col), for a panic rustc reports there. */
static lust_loc lust_std_loc(uint32_t file, uint32_t line, uint32_t col) {
    return (((uint64_t)(LUST_STD_SLOT + file)) << 40) | ((uint64_t)line << 20) | (uint64_t)col;
}

/* The `start..end` of a `RangeBounds<usize>` argument (tags: 0 Included,
   1 Excluded, 2 Unbounded), checked the way core checks it for
   `Vec::drain` and `String::drain`: the end bound against the length
   first, then the start bound, then their order, with core's exact
   panic texts. An excluded start at the end index fails with the end
   message, as in core. The panics report core's own sites in
   slice/index.rs (`into_slice_range`, std file 12), not the caller:
   `slice::range` is track_caller to there, and `Vec::drain` is not
   track_caller at all. */
static void lust_range_bounds_check(uint64_t len, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, uint64_t *out_s, uint64_t *out_e) LUST_BODY({
    uint64_t end;
    if (e_tag == 0) {
        if (e_val >= len) {
            lust_String s = lust_string_new();
            lust_string_push_cstr(&s, "range end index ");
            lust_fmt_u64(&s, e_val);
            lust_string_push_cstr(&s, " out of range for slice of length ");
            lust_fmt_u64(&s, len);
            lust_panic(&s, lust_std_loc(12, 1005, 52));
        }
        end = e_val + 1;
    } else if (e_tag == 1) {
        if (e_val > len) {
            lust_String s = lust_string_new();
            lust_string_push_cstr(&s, "range end index ");
            lust_fmt_u64(&s, e_val);
            lust_string_push_cstr(&s, " out of range for slice of length ");
            lust_fmt_u64(&s, len);
            lust_panic(&s, lust_std_loc(12, 1009, 51));
        }
        end = e_val;
    } else {
        end = len;
    }
    uint64_t start;
    if (s_tag == 2) {
        start = 0;
    } else {
        /* Core's start match: Excluded fails at index.rs:1016,
           Included at 1020, for every start failure. */
        lust_loc start_loc = s_tag == 1 ? lust_std_loc(12, 1016, 56) : lust_std_loc(12, 1020, 55);
        if (s_val > len) {
            lust_String s = lust_string_new();
            lust_string_push_cstr(&s, "range start index ");
            lust_fmt_u64(&s, s_val);
            lust_string_push_cstr(&s, " out of range for slice of length ");
            lust_fmt_u64(&s, len);
            lust_panic(&s, start_loc);
        }
        if (s_tag == 1 && s_val == end) {
            lust_String s = lust_string_new();
            lust_string_push_cstr(&s, "range end index ");
            lust_fmt_u64(&s, s_val);
            lust_string_push_cstr(&s, " out of range for slice of length ");
            lust_fmt_u64(&s, len);
            lust_panic(&s, start_loc);
        }
        if (s_val > end) {
            lust_String s = lust_string_new();
            lust_string_push_cstr(&s, "slice index starts at ");
            lust_fmt_u64(&s, s_val);
            lust_string_push_cstr(&s, " but ends at ");
            lust_fmt_u64(&s, end);
            lust_panic(&s, start_loc);
        }
        start = s_tag == 1 ? s_val + 1 : s_val;
    }
    *out_s = start;
    *out_e = end;
})

/* `Vec::drain`: the Vec keeps its buffer and capacity; its length is the
   drain start while the Drain lives (a leaked Drain leaves it so). This form is for
   flag-mode unwinding (lust_unwind_mode 1), where a panic returns with the thread's
   panic pending; codegen calls lust_vec_drain_t in every other build. */
lust_VecDrain lust_vec_drain(lust_Vec *v, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, lust_loc loc) LUST_BODY({
    (void)loc; /* range panics report core's slice/index.rs sites */
    uint64_t start, end;
    lust_range_bounds_check(v->len, s_tag, s_val, e_tag, e_val, &start, &end);
    if (lust_unwind_mode && lust_unw_mine()) {
        /* The range panicked: the Vec stays as it is (an empty Drain at its end). */
        lust_VecDrain e = {v, v->len, v->len, v->len, v->len, 0};
        return e;
    }
    lust_VecDrain d = {v, start, start, end, end, v->len - end};
    v->len = start;
    return d;
})

/* `Vec::drain` where a panic never returns (panic=abort, or unwind tables: it throws):
   no check of the thread's pending panic, which is a thread-local lookup per drain. */
lust_VecDrain lust_vec_drain_t(lust_Vec *v, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, lust_loc loc) LUST_BODY({
    (void)loc;
    uint64_t start, end;
    lust_range_bounds_check(v->len, s_tag, s_val, e_tag, e_val, &start, &end);
    lust_VecDrain d = {v, start, start, end, end, v->len - end};
    v->len = start;
    return d;
})

/* `String::drain`: the same range checks over the byte length, then the
   char boundary asserts. The String is unchanged while the Drain lives
   (a leaked Drain leaves it whole); the drop glue removes the range. `flag`: flag-mode
   unwinding, where the range check's panic returns pending (lust_string_drain); 0 in
   every other build (lust_string_drain_t), where it never returns. */
static lust_VecDrain lust_string_drain_in(lust_String *v, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, lust_loc loc, int flag) LUST_BODY({
    uint64_t start, end;
    lust_range_bounds_check(v->len, s_tag, s_val, e_tag, e_val, &start, &end);
    lust_VecDrain e = {v, v->len, v->len, v->len, v->len, 0}; /* after a panic: an empty Drain at the end */
    if (flag && lust_unwind_mode && lust_unw_mine()) return e;
    if (!(start == v->len || (v->ptr[start] & 0xC0) != 0x80)) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "assertion failed: self.is_char_boundary(start)");
        lust_panic(&s, loc);
        return e;
    }
    if (!(end == v->len || (v->ptr[end] & 0xC0) != 0x80)) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "assertion failed: self.is_char_boundary(end)");
        lust_panic(&s, loc);
        return e;
    }
    lust_VecDrain d = {v, start, start, end, end, v->len - end};
    return d;
})

lust_VecDrain lust_string_drain(lust_String *v, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, lust_loc loc) LUST_BODY({
    return lust_string_drain_in(v, s_tag, s_val, e_tag, e_val, loc, 1);
})

lust_VecDrain lust_string_drain_t(lust_String *v, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, lust_loc loc) LUST_BODY({
    return lust_string_drain_in(v, s_tag, s_val, e_tag, e_val, loc, 0);
})

/* `slice::range(r, ..len)` for the callers outside this file
   (`Vec::extend_from_within`): drain's four range words checked at
   core's index.rs sites (`lust_range_bounds_check`). */
void lust_range_check(uint64_t len, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, uint64_t *out_s, uint64_t *out_e) LUST_BODY({
    lust_range_bounds_check(len, s_tag, s_val, e_tag, e_val, out_s, out_e);
})

/* `[u8]::eq_ignore_ascii_case`: equal lengths and every byte pair equal
   after ASCII lowercasing. */
uint8_t lust_bytes_eq_ignore_ascii_case(const uint8_t *a, uint64_t an, const uint8_t *b, uint64_t bn) LUST_BODY({
    if (an != bn) return 0;
    for (uint64_t i = 0; i < an; i++) {
        uint8_t x = a[i], y = b[i];
        if (x >= 'A' && x <= 'Z') x += 32;
        if (y >= 'A' && y <= 'Z') y += 32;
        if (x != y) return 0;
    }
    return 1;
})

/* `[u8]::is_ascii` and `str::is_ascii`: no byte at or above 0x80. A clang or gcc build for
   x86_64 tests 32 bytes a step (two 16-byte loads, one sign-bit mask) and ends with one
   16-byte load at the last byte (it may test some bytes twice); other builds test 8 bytes a
   word. It never reads outside the n bytes. */
#if !defined(__TINYC__) && defined(__x86_64__) && defined(__SSE2__)
typedef char lust_v16_ __attribute__((vector_size(16)));
typedef char lust_v16u_ __attribute__((vector_size(16), aligned(1)));
#endif
uint8_t lust_bytes_is_ascii(const uint8_t *p, uint64_t n) LUST_BODY({
#if !defined(__TINYC__) && defined(__x86_64__) && defined(__SSE2__)
    if (n >= 16) {
        const uint8_t *q = p, *last = p + n - 16;
        for (; q + 16 < last; q += 32) {
            lust_v16_ a = *(const lust_v16u_ *)(const void *)q, b = *(const lust_v16u_ *)(const void *)(q + 16);
            if (__builtin_ia32_pmovmskb128(a | b)) return 0;
        }
        if (q < last) {
            lust_v16_ a = *(const lust_v16u_ *)(const void *)q;
            if (__builtin_ia32_pmovmskb128(a)) return 0;
        }
        lust_v16_ z = *(const lust_v16u_ *)(const void *)last;
        return !__builtin_ia32_pmovmskb128(z);
    }
#endif
    uint64_t i = 0;
    for (; i + 8 <= n; i += 8) {
        uint64_t w;
        memcpy(&w, p + i, 8);
        if (w & 0x8080808080808080ull) return 0;
    }
    for (; i < n; i++)
        if (p[i] >= 0x80) return 0;
    return 1;
})

/* `[T]::rotate_left(mid)` over `len` elements of `elem` bytes, after the
   caller's assert: three reversals, elements moved as bytes. */
void lust_slice_rotate_left(void *ptr, uint64_t len, uint64_t elem, uint64_t mid) LUST_BODY({
    uint8_t *p = (uint8_t *)ptr;
    uint64_t spans[3][2] = {{0, mid}, {mid, len}, {0, len}};
    for (int k = 0; k < 3; k++) {
        uint64_t lo = spans[k][0], hi = spans[k][1];
        while (lo + 1 < hi) {
            hi--;
            for (uint64_t b = 0; b < elem; b++) {
                uint8_t t = p[lo * elem + b];
                p[lo * elem + b] = p[hi * elem + b];
                p[hi * elem + b] = t;
            }
            lo++;
        }
    }
})

/* `[T]::copy_within` over a byte buffer of `len` elements of `elem`
   bytes: core checks the range as for drain (`lust_range_bounds_check`,
   core's own panic sites), then the destination against the space
   the copied range leaves (`dest is out of bounds` at the caller,
   core's `#[track_caller]` assert), then moves the bytes, overlap
   included. */
/* One `Utf8Chunks` step (core's `str::lossy` scan, byte for byte):
   writes the valid prefix length and the total inspected length
   (valid + the broken sequence, at most 3 more bytes) of `p[..len]`.
   The caller guarantees `len > 0`. A read past the end answers 0,
   which fails every continuation test, as core's `safe_get` does. */
void lust_utf8_chunk_step(const uint8_t *p, uint64_t len, uint64_t *valid, uint64_t *used) LUST_BODY({
    uint64_t i = 0;
    uint64_t valid_up_to = 0;
    while (i < len) {
        uint8_t byte = p[i];
        i += 1;
        if (byte >= 128) {
            uint8_t b1 = i < len ? p[i] : 0;
            if (byte >= 0xC2 && byte <= 0xDF) {
                if ((b1 & 192) != 128) break;
                i += 1;
            } else if (byte >= 0xE0 && byte <= 0xEF) {
                int ok = (byte == 0xE0 && b1 >= 0xA0 && b1 <= 0xBF) || (byte >= 0xE1 && byte <= 0xEC && b1 >= 0x80 && b1 <= 0xBF) ||
                         (byte == 0xED && b1 >= 0x80 && b1 <= 0x9F) || (byte >= 0xEE && b1 >= 0x80 && b1 <= 0xBF);
                if (!ok) break;
                i += 1;
                if (((i < len ? p[i] : 0) & 192) != 128) break;
                i += 1;
            } else if (byte >= 0xF0 && byte <= 0xF4) {
                int ok = (byte == 0xF0 && b1 >= 0x90 && b1 <= 0xBF) || (byte >= 0xF1 && byte <= 0xF3 && b1 >= 0x80 && b1 <= 0xBF) ||
                         (byte == 0xF4 && b1 >= 0x80 && b1 <= 0x8F);
                if (!ok) break;
                i += 1;
                if (((i < len ? p[i] : 0) & 192) != 128) break;
                i += 1;
                if (((i < len ? p[i] : 0) & 192) != 128) break;
                i += 1;
            } else {
                break;
            }
        }
        valid_up_to = i;
    }
    *valid = valid_up_to;
    *used = i;
})

/* The `start..end` of a `SliceIndex` range argument (same tags as
   `lust_range_bounds_check`), or 0 when core's `get` would answer
   `None`: the end bound against the length first, then the start
   bound, then their order (core's `try_into_slice_range`). */
int lust_range_bounds_get(uint64_t len, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, uint64_t *out_s, uint64_t *out_e) LUST_BODY({
    uint64_t end;
    if (e_tag == 0) {
        if (e_val >= len) return 0;
        end = e_val + 1;
    } else if (e_tag == 1) {
        if (e_val > len) return 0;
        end = e_val;
    } else {
        end = len;
    }
    uint64_t start;
    if (s_tag == 2) {
        start = 0;
    } else if (s_tag == 1) {
        if (s_val >= end) return 0;
        start = s_val + 1;
    } else {
        if (s_val > end) return 0;
        start = s_val;
    }
    *out_s = start;
    *out_e = end;
    return 1;
})

void lust_slice_copy_within(void *ptr, uint64_t len, uint64_t elem, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val, uint64_t dest, lust_loc loc) LUST_BODY({
    uint64_t start, end;
    lust_range_bounds_check(len, s_tag, s_val, e_tag, e_val, &start, &end);
    if (lust_unwind_mode && lust_unw_mine()) return;
    if (dest > len - (end - start)) {
        lust_panic_cstr("dest is out of bounds", loc);
        return;
    }
    memmove((char *)ptr + dest * elem, (char *)ptr + start * elem, (end - start) * elem);
})

/* Exact float remainder (Rust `%`, truncating division), computed on the
   mantissa integers so no libm link is needed. The algorithm is the
   standard normalize-and-subtract loop over the exponent difference. */
double lust_fmod_f64(double x, double y) LUST_BODY({
    union { double f; uint64_t i; } ux, uy;
    ux.f = x;
    uy.f = y;
    int ex = (int)((ux.i >> 52) & 0x7ff);
    int ey = (int)((uy.i >> 52) & 0x7ff);
    uint64_t sx = ux.i >> 63;
    uint64_t ax = ux.i & (UINT64_MAX >> 1);
    uint64_t ay = uy.i & (UINT64_MAX >> 1);
    ux.i &= (1ULL << 52) - 1;
    uy.i &= (1ULL << 52) - 1;
    if (ay == 0 || ex == 0x7ff || (ey == 0x7ff && (ay & ((1ULL << 52) - 1)) != 0) || ax > 0x7ff0000000000000ULL) {
        return (x * y) / (x * y); /* NaN */
    }
    if (ax <= ay) {
        if (ax == ay) {
            ux.f = 0.0;
            ux.i |= sx << 63;
            return ux.f;
        }
        return x;
    }
    /* Normalize both mantissas to 53-bit integers. */
    if (ex == 0) {
        uint64_t i = ux.i;
        for (; !(i >> 52); i <<= 1) ex--;
        ux.i = i;
        ex += 1;
    } else {
        ux.i |= 1ULL << 52;
    }
    if (ey == 0) {
        uint64_t i = uy.i;
        for (; !(i >> 52); i <<= 1) ey--;
        uy.i = i;
        ey += 1;
    } else {
        uy.i |= 1ULL << 52;
    }
    for (; ex > ey; ex--) {
        if (ux.i >= uy.i) {
            ux.i -= uy.i;
            if (ux.i == 0) {
                ux.f = 0.0;
                ux.i |= sx << 63;
                return ux.f;
            }
        }
        ux.i <<= 1;
    }
    if (ux.i >= uy.i) {
        ux.i -= uy.i;
        if (ux.i == 0) {
            ux.f = 0.0;
            ux.i |= sx << 63;
            return ux.f;
        }
    }
    while (!(ux.i >> 52)) {
        ux.i <<= 1;
        ey--;
    }
    if (ey > 0) {
        ux.i -= 1ULL << 52;
        ux.i |= (uint64_t)ey << 52;
    } else {
        ux.i >>= (uint64_t)(1 - ey);
    }
    ux.i |= sx << 63;
    return ux.f;
})

float lust_fmod_f32(float x, float y) LUST_BODY({
    /* The f64 remainder of two f32 values is exact, and its result is an
       f32 value, so one rounding at the end is exact. */
    return (float)lust_fmod_f64((double)x, (double)y);
})

uint64_t lust_bounds(uint64_t i, uint64_t len, lust_loc loc) LUST_BODY({
    if (i >= len) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "index out of bounds: the len is ");
        lust_fmt_u64(&s, len);
        lust_string_push_cstr(&s, " but the index is ");
        lust_fmt_u64(&s, i);
        lust_panic_dyn(&s, loc);
    }
    return i;
})

/* ---------- Checked integer math ---------- */

#define LUST_OVF(op) lust_ovf(op, loc)

/* Narrow signed types: compute exactly in int64_t, then range check. */
#define LUST_SIGNED_NARROW(T, N, MINV, MAXV) \
T lust_add_##N(T a, T b, lust_loc loc) LUST_BODY({ int64_t r = (int64_t)a + b; if (r < MINV || r > MAXV) LUST_OVF("add"); return (T)r; }) \
T lust_sub_##N(T a, T b, lust_loc loc) LUST_BODY({ int64_t r = (int64_t)a - b; if (r < MINV || r > MAXV) LUST_OVF("subtract"); return (T)r; }) \
T lust_mul_##N(T a, T b, lust_loc loc) LUST_BODY({ int64_t r = (int64_t)a * b; if (r < MINV || r > MAXV) LUST_OVF("multiply"); return (T)r; }) \
T lust_neg_##N(T a, lust_loc loc) LUST_BODY({ if (a == MINV) { LUST_OVF("negate"); return a; } return (T)-a; }) \
T lust_div_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b == 0) { lust_panic_cstr("attempt to divide by zero", loc); return 0; } if (a == MINV && b == -1) { LUST_OVF("divide"); return 0; } return (T)(a / b); }) \
T lust_rem_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b == 0) { lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return 0; } if (a == MINV && b == -1) { LUST_OVF("calculate the remainder"); return 0; } return (T)(a % b); })

#define LUST_UNSIGNED_NARROW(T, N, MAXV) \
T lust_add_##N(T a, T b, lust_loc loc) LUST_BODY({ uint64_t r = (uint64_t)a + b; if (r > MAXV) LUST_OVF("add"); return (T)r; }) \
T lust_sub_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b > a) LUST_OVF("subtract"); return (T)(a - b); }) \
T lust_mul_##N(T a, T b, lust_loc loc) LUST_BODY({ uint64_t r = (uint64_t)a * (uint64_t)b; if (r > MAXV) LUST_OVF("multiply"); return (T)r; }) \
T lust_div_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b == 0) { lust_panic_cstr("attempt to divide by zero", loc); return 0; } return (T)(a / b); }) \
T lust_rem_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b == 0) { lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return 0; } return (T)(a % b); })

LUST_SIGNED_NARROW(int8_t, i8, -128, 127)
LUST_SIGNED_NARROW(int16_t, i16, -32768, 32767)
LUST_SIGNED_NARROW(int32_t, i32, -2147483647 - 1, 2147483647)
LUST_UNSIGNED_NARROW(uint8_t, u8, 255u)
LUST_UNSIGNED_NARROW(uint16_t, u16, 65535u)
LUST_UNSIGNED_NARROW(uint32_t, u32, 4294967295u)

int64_t lust_add_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    int64_t r = (int64_t)((uint64_t)a + (uint64_t)b);
    if (((a ^ r) & (b ^ r)) < 0) LUST_OVF("add");
    return r;
})
int64_t lust_sub_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    int64_t r = (int64_t)((uint64_t)a - (uint64_t)b);
    if (((a ^ b) & (a ^ r)) < 0) LUST_OVF("subtract");
    return r;
})
int64_t lust_mul_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    if (a == 0 || b == 0) return 0;
    if ((a == -1 && b == INT64_MIN) || (b == -1 && a == INT64_MIN)) LUST_OVF("multiply");
    int64_t r = (int64_t)((uint64_t)a * (uint64_t)b);
    if (r / b != a) LUST_OVF("multiply");
    return r;
})
int64_t lust_neg_i64(int64_t a, lust_loc loc) LUST_BODY({ if (a == INT64_MIN) { LUST_OVF("negate"); return a; } return -a; })
int64_t lust_div_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    if (b == 0) { lust_panic_cstr("attempt to divide by zero", loc); return 0; }
    if (a == INT64_MIN && b == -1) { LUST_OVF("divide"); return 0; }
    return a / b;
})
int64_t lust_rem_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    if (b == 0) { lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return 0; }
    if (a == INT64_MIN && b == -1) { LUST_OVF("calculate the remainder"); return 0; }
    return a % b;
})
uint64_t lust_add_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ uint64_t r = a + b; if (r < a) LUST_OVF("add"); return r; })
uint64_t lust_sub_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ if (b > a) LUST_OVF("subtract"); return a - b; })
uint64_t lust_mul_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ uint64_t r = a * b; if (a != 0 && r / a != b) LUST_OVF("multiply"); return r; })
uint64_t lust_div_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ if (b == 0) { lust_panic_cstr("attempt to divide by zero", loc); return 0; } return a / b; })
uint64_t lust_rem_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ if (b == 0) { lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return 0; } return a % b; })

uint32_t lust_shift_amount(uint64_t b, uint32_t bits, const char *op, lust_loc loc) LUST_BODY({
    if (b >= bits) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "attempt to shift ");
        lust_string_push_cstr(&s, op);
        lust_string_push_cstr(&s, " with overflow");
        lust_panic_lit(&s, loc);
        return 0;
    }
    return (uint32_t)b;
})

#define LUST_POW(T, N) \
T lust_pow_##N(T a, uint32_t e, lust_loc loc) LUST_BODY({ \
    T r = 1; \
    while (e) { if (e & 1) r = lust_mul_##N(r, a, loc); e >>= 1; if (e) a = lust_mul_##N(a, a, loc); } \
    return r; \
})
#define LUST_ABS(T, N) T lust_abs_##N(T a, lust_loc loc) LUST_BODY({ return a < 0 ? lust_neg_##N(a, loc) : a; })
LUST_POW(int8_t, i8) LUST_POW(int16_t, i16) LUST_POW(int32_t, i32) LUST_POW(int64_t, i64)
LUST_POW(uint8_t, u8) LUST_POW(uint16_t, u16) LUST_POW(uint32_t, u32) LUST_POW(uint64_t, u64)
LUST_ABS(int8_t, i8) LUST_ABS(int16_t, i16) LUST_ABS(int32_t, i32) LUST_ABS(int64_t, i64)

/* ---------- Checked, saturating, and bit ops on 64-bit words ----------
   One generic form for the checked_* and overflowing_* methods:
   operands arrive masked to the operand width (sign bits above the
   width are the caller's to mask off first), the result leaves
   masked the same way. Returns 1 on success, 0 on overflow (the
   wrapping result is still in *out), and -1 for division by zero.
   Ops: 0 add, 1 sub, 2 mul, 3 div, 4 rem. */

static uint64_t lust_mask64(unsigned bits) LUST_BODY({
    return bits >= 64 ? ~0ull : ((1ull << bits) - 1ull);
})
static int64_t lust_sext64(uint64_t v, unsigned bits) LUST_BODY({
    if (bits >= 64) return (int64_t)v;
    if (v & (1ull << (bits - 1))) return (int64_t)(v | ~lust_mask64(bits));
    return (int64_t)v;
})

int lust_checked_op(uint64_t a, uint64_t b, unsigned bits, int is_signed, int op, uint64_t *out) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    a &= mask;
    b &= mask;
    if (is_signed) {
        int64_t sa = lust_sext64(a, bits), sb = lust_sext64(b, bits);
        int64_t minv = bits >= 64 ? INT64_MIN : -(1ll << (bits - 1));
        int64_t maxv = bits >= 64 ? INT64_MAX : ((1ll << (bits - 1)) - 1);
        int64_t r = 0;
        int ok = 1;
        switch (op) {
            case 0:
                r = (int64_t)((uint64_t)sa + (uint64_t)sb);
                ok = bits < 64 ? (r >= minv && r <= maxv) : !(((sa ^ r) & (sb ^ r)) < 0);
                break;
            case 1:
                r = (int64_t)((uint64_t)sa - (uint64_t)sb);
                ok = bits < 64 ? (r >= minv && r <= maxv) : !(((sa ^ sb) & (sa ^ r)) < 0);
                break;
            case 2:
                r = (int64_t)((uint64_t)sa * (uint64_t)sb);
                if (bits < 64) {
                    ok = (r >= minv && r <= maxv);
                } else if (sa == 0 || sb == 0) {
                    ok = 1;
                } else if ((sa == -1 && sb == INT64_MIN) || (sb == -1 && sa == INT64_MIN)) {
                    ok = 0;
                } else {
                    ok = (r / sb == sa);
                }
                break;
            case 3:
            case 4:
                if (sb == 0) return -1;
                if (sa == minv && sb == -1) {
                    *out = (op == 3 ? (uint64_t)sa : 0ull) & mask;
                    return 0;
                }
                r = op == 3 ? sa / sb : sa % sb;
                break;
            default:
                return 0;
        }
        *out = (uint64_t)r & mask;
        return ok;
    }
    {
        uint64_t r = 0;
        int ok = 1;
        switch (op) {
            case 0:
                r = a + b;
                ok = bits < 64 ? (r <= mask) : (r >= a);
                break;
            case 1:
                r = a - b;
                ok = (a >= b);
                break;
            case 2:
                r = a * b;
                ok = bits < 64 ? (r <= mask) : (a == 0 || r / a == b);
                break;
            case 3:
                if (b == 0) return -1;
                r = a / b;
                break;
            case 4:
                if (b == 0) return -1;
                r = a % b;
                break;
            default:
                return 0;
        }
        *out = r & mask;
        return ok;
    }
})

/* checked_pow on the same representation: squaring loop, and the
   final unused square is not computed, as in core. */
int lust_checked_pow(uint64_t a, uint32_t e, unsigned bits, int is_signed, uint64_t *out) LUST_BODY({
    uint64_t r = 1, x = a & lust_mask64(bits), t;
    while (e) {
        if (e & 1) {
            if (!lust_checked_op(r, x, bits, is_signed, 2, &t)) {
                *out = t;
                return 0;
            }
            r = t;
        }
        e >>= 1;
        if (!e) break;
        if (!lust_checked_op(x, x, bits, is_signed, 2, &t)) {
            *out = t;
            return 0;
        }
        x = t;
    }
    *out = r;
    return 1;
})

/* wrapping_pow on the same representation: no checks at all. */
uint64_t lust_wrapping_pow(uint64_t a, uint32_t e, unsigned bits) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    uint64_t r = 1, x = a & mask;
    while (e) {
        if (e & 1) r = (r * x) & mask;
        e >>= 1;
        if (!e) break;
        x = (x * x) & mask;
    }
    return r & mask;
})

/* Euclid division: the quotient rounds toward negative infinity,
   the remainder is never negative. Both panic exactly as the plain
   operators do for a zero divisor and for MIN / -1. */
/* Unsigned ceiling division (div_ceil): a / b rounded up. The
   quotient-plus-remainder form cannot overflow. */
uint64_t lust_div_ceil(uint64_t a, uint64_t b, unsigned bits, lust_loc loc) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    a &= mask;
    b &= mask;
    if (b == 0) { lust_panic_cstr("attempt to divide by zero", loc); return 0; }
    return a / b + (a % b != 0);
})

uint64_t lust_div_euclid(uint64_t a, uint64_t b, unsigned bits, int is_signed, lust_loc loc) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    a &= mask;
    b &= mask;
    if (!is_signed) {
        if (b == 0) { lust_panic_cstr("attempt to divide by zero", loc); return 0; }
        return a / b;
    }
    {
        int64_t sa = lust_sext64(a, bits), sb = lust_sext64(b, bits);
        int64_t minv = bits >= 64 ? INT64_MIN : -(1ll << (bits - 1));
        int64_t q;
        if (sb == 0) { lust_panic_cstr("attempt to divide by zero", loc); return 0; }
        if (sa == minv && sb == -1) { LUST_OVF("divide"); return 0; }
        q = sa / sb;
        if (sa % sb < 0) q += sb > 0 ? -1 : 1;
        return (uint64_t)q & mask;
    }
})
uint64_t lust_rem_euclid(uint64_t a, uint64_t b, unsigned bits, int is_signed, lust_loc loc) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    a &= mask;
    b &= mask;
    if (!is_signed) {
        if (b == 0) { lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return 0; }
        return a % b;
    }
    {
        int64_t sa = lust_sext64(a, bits), sb = lust_sext64(b, bits);
        int64_t minv = bits >= 64 ? INT64_MIN : -(1ll << (bits - 1));
        int64_t r;
        if (sb == 0) { lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return 0; }
        if (sa == minv && sb == -1) { LUST_OVF("calculate the remainder"); return 0; }
        r = sa % sb;
        if (r < 0) r += sb > 0 ? sb : -sb;
        return (uint64_t)r & mask;
    }
})

uint64_t lust_isqrt64(uint64_t v) LUST_BODY({
    uint64_t r = 1ull << 32, n;
    if (v < 2) return v;
    for (;;) {
        n = (r + v / r) / 2;
        if (n >= r) return r;
        r = n;
    }
})
uint32_t lust_count_ones64(uint64_t v) LUST_BODY({
    v = v - ((v >> 1) & 0x5555555555555555ull);
    v = (v & 0x3333333333333333ull) + ((v >> 2) & 0x3333333333333333ull);
    v = (v + (v >> 4)) & 0x0F0F0F0F0F0F0F0Full;
    return (uint32_t)((v * 0x0101010101010101ull) >> 56);
})
uint32_t lust_leading_zeros64(uint64_t v, unsigned bits) LUST_BODY({
    uint32_t n = 0;
    int i;
    if (v == 0) return bits;
    for (i = 63; i >= 0 && !((v >> i) & 1ull); i--) n++;
    return n - (64 - bits);
})
uint32_t lust_trailing_zeros64(uint64_t v, unsigned bits) LUST_BODY({
    uint32_t n = 0;
    unsigned i;
    if (v == 0) return bits;
    for (i = 0; i < bits && !((v >> i) & 1ull); i++) n++;
    return n;
})

/* ---------- 128-bit integers ---------- */

/* Two-word helpers over lust_u128/lust_i128. Division is Knuth's
   Algorithm D over 32-bit limbs (the spike's bit-by-bit divider took
   1673 ns; this one is two orders of magnitude less), and formatting
   divides by 10^19 chunks through the 128-by-64 fast path. Checked
   wrappers panic with the same texts as the narrow types above. */

lust_u128 lust_u128_from_i128(lust_i128 a) LUST_BODY({ lust_u128 r; r.lo = a.lo; r.hi = a.hi; return r; })
lust_i128 lust_i128_from_u128(lust_u128 a) LUST_BODY({ lust_i128 r; r.lo = a.lo; r.hi = a.hi; return r; })

lust_u128 lust_u128_add(lust_u128 a, lust_u128 b) LUST_BODY({
    lust_u128 r;
    r.lo = a.lo + b.lo;
    r.hi = a.hi + b.hi + (r.lo < a.lo);
    return r;
})
lust_u128 lust_u128_sub(lust_u128 a, lust_u128 b) LUST_BODY({
    lust_u128 r;
    r.lo = a.lo - b.lo;
    r.hi = a.hi - b.hi - (a.lo < b.lo);
    return r;
})
lust_i128 lust_i128_add(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_add(lust_u128_from_i128(a), lust_u128_from_i128(b))); })
lust_i128 lust_i128_sub(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_sub(lust_u128_from_i128(a), lust_u128_from_i128(b))); })

int32_t lust_u128_cmp(lust_u128 a, lust_u128 b) LUST_BODY({
    if (a.hi != b.hi) return a.hi < b.hi ? -1 : 1;
    if (a.lo != b.lo) return a.lo < b.lo ? -1 : 1;
    return 0;
})
int32_t lust_i128_cmp(lust_i128 a, lust_i128 b) LUST_BODY({
    int64_t ah = (int64_t)a.hi, bh = (int64_t)b.hi;
    if (ah != bh) return ah < bh ? -1 : 1;
    if (a.lo != b.lo) return a.lo < b.lo ? -1 : 1;
    return 0;
})

lust_u128 lust_u128_and(lust_u128 a, lust_u128 b) LUST_BODY({ lust_u128 r; r.lo = a.lo & b.lo; r.hi = a.hi & b.hi; return r; })
lust_u128 lust_u128_or(lust_u128 a, lust_u128 b) LUST_BODY({ lust_u128 r; r.lo = a.lo | b.lo; r.hi = a.hi | b.hi; return r; })
lust_u128 lust_u128_xor(lust_u128 a, lust_u128 b) LUST_BODY({ lust_u128 r; r.lo = a.lo ^ b.lo; r.hi = a.hi ^ b.hi; return r; })
lust_u128 lust_u128_not(lust_u128 a) LUST_BODY({ lust_u128 r; r.lo = ~a.lo; r.hi = ~a.hi; return r; })
lust_i128 lust_i128_and(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_and(lust_u128_from_i128(a), lust_u128_from_i128(b))); })
lust_i128 lust_i128_or(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_or(lust_u128_from_i128(a), lust_u128_from_i128(b))); })
lust_i128 lust_i128_xor(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_xor(lust_u128_from_i128(a), lust_u128_from_i128(b))); })
lust_i128 lust_i128_not(lust_i128 a) LUST_BODY({ return lust_i128_from_u128(lust_u128_not(lust_u128_from_i128(a))); })

/* Full 64x64->128 product through 32-bit halves. Returns the low word;
   the high word goes to *hi. */
uint64_t lust_u128_mul64(uint64_t a, uint64_t b, uint64_t *hi) LUST_BODY({
    uint64_t al = a & 0xFFFFFFFFull, ah = a >> 32;
    uint64_t bl = b & 0xFFFFFFFFull, bh = b >> 32;
    uint64_t ll = al * bl, lh = al * bh, hl = ah * bl, hh = ah * bh;
    uint64_t mid = lh + (ll >> 32) + (hl & 0xFFFFFFFFull);
    *hi = hh + (hl >> 32) + (mid >> 32);
    return (mid << 32) | (ll & 0xFFFFFFFFull);
})

lust_u128 lust_u128_mul(lust_u128 a, lust_u128 b) LUST_BODY({
    lust_u128 r;
    uint64_t hi;
    r.lo = lust_u128_mul64(a.lo, b.lo, &hi);
    r.hi = hi + a.lo * b.hi + a.hi * b.lo;
    return r;
})
lust_i128 lust_i128_mul(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_mul(lust_u128_from_i128(a), lust_u128_from_i128(b))); })

lust_u128 lust_u128_shl(lust_u128 a, uint32_t n) LUST_BODY({
    lust_u128 r;
    if (n >= 64) { r.lo = 0; r.hi = a.lo << (n - 64); }
    else if (n) { r.lo = a.lo << n; r.hi = (a.hi << n) | (a.lo >> (64 - n)); }
    else r = a;
    return r;
})
lust_u128 lust_u128_shr(lust_u128 a, uint32_t n) LUST_BODY({
    lust_u128 r;
    if (n >= 64) { r.lo = a.hi >> (n - 64); r.hi = 0; }
    else if (n) { r.lo = (a.lo >> n) | (a.hi << (64 - n)); r.hi = a.hi >> n; }
    else r = a;
    return r;
})
lust_i128 lust_i128_shl(lust_i128 a, uint32_t n) LUST_BODY({ return lust_i128_from_u128(lust_u128_shl(lust_u128_from_i128(a), n)); })
lust_i128 lust_i128_shr(lust_i128 a, uint32_t n) LUST_BODY({
    lust_i128 r;
    if (n >= 64) { r.lo = (uint64_t)((int64_t)a.hi >> (n - 64)); r.hi = (uint64_t)((int64_t)a.hi >> 63); }
    else if (n) { r.lo = (a.lo >> n) | (a.hi << (64 - n)); r.hi = (uint64_t)((int64_t)a.hi >> n); }
    else r = a;
    return r;
})

uint32_t lust_u128_clz32(uint32_t x) LUST_BODY({
    uint32_t n = 0;
    if (!(x >> 16)) { n += 16; x <<= 16; }
    if (!(x >> 24)) { n += 8; x <<= 8; }
    if (!(x >> 28)) { n += 4; x <<= 4; }
    if (!(x >> 30)) { n += 2; x <<= 2; }
    if (!(x >> 31)) n += 1;
    return n;
})

/* Unsigned 128/128. The caller guarantees b != 0. A one-limb divisor
   takes the schoolbook loop; wider divisors take Knuth's Algorithm D
   in base 2^32. */
lust_u128 lust_u128_divmod(lust_u128 a, lust_u128 b, lust_u128 *rem) LUST_BODY({
    if (lust_u128_cmp(a, b) < 0) {
        if (rem) *rem = a;
        lust_u128 z = {0, 0};
        return z;
    }
    uint32_t bl[4] = {(uint32_t)b.lo, (uint32_t)(b.lo >> 32), (uint32_t)b.hi, (uint32_t)(b.hi >> 32)};
    uint32_t al[4] = {(uint32_t)a.lo, (uint32_t)(a.lo >> 32), (uint32_t)a.hi, (uint32_t)(a.hi >> 32)};
    if (!bl[1] && !bl[2] && !bl[3]) {
        uint64_t d = bl[0], r = 0;
        uint32_t q[4];
        for (int i = 3; i >= 0; i--) {
            uint64_t t = (r << 32) | al[i];
            q[i] = (uint32_t)(t / d);
            r = t - (uint64_t)q[i] * d;
        }
        if (rem) { rem->lo = r; rem->hi = 0; }
        lust_u128 out;
        out.lo = (uint64_t)q[0] | ((uint64_t)q[1] << 32);
        out.hi = (uint64_t)q[2] | ((uint64_t)q[3] << 32);
        return out;
    }
    uint32_t u[5], v[4], q[4] = {0, 0, 0, 0};
    int n = bl[3] ? 4 : bl[2] ? 3 : 2;
    int m = 4;
    uint32_t s = lust_u128_clz32(bl[n - 1]);
    for (int i = n - 1; i > 0; i--) v[i] = s ? (bl[i] << s) | (bl[i - 1] >> (32 - s)) : bl[i];
    v[0] = bl[0] << s;
    u[4] = s ? al[3] >> (32 - s) : 0;
    for (int i = 3; i > 0; i--) u[i] = s ? (al[i] << s) | (al[i - 1] >> (32 - s)) : al[i];
    u[0] = al[0] << s;
    for (int j = m - n; j >= 0; j--) {
        uint64_t num = ((uint64_t)u[j + n] << 32) | u[j + n - 1];
        uint64_t qhat = num / v[n - 1];
        uint64_t rhat = num - qhat * v[n - 1];
        for (;;) {
            if (qhat > 0xFFFFFFFFull || qhat * v[n - 2] > ((rhat << 32) | u[j + n - 2])) {
                qhat--;
                rhat += v[n - 1];
                if (rhat <= 0xFFFFFFFFull) continue;
            }
            break;
        }
        int64_t borrow = 0;
        uint64_t carry = 0;
        for (int k = 0; k < n; k++) {
            uint64_t p = qhat * v[k] + carry;
            carry = p >> 32;
            int64_t t = (int64_t)u[j + k] - borrow - (int64_t)(uint32_t)p;
            u[j + k] = (uint32_t)t;
            borrow = t < 0 ? 1 : 0;
        }
        int64_t t = (int64_t)u[j + n] - borrow - (int64_t)carry;
        u[j + n] = (uint32_t)t;
        q[j] = (uint32_t)qhat;
        if (t < 0) {
            q[j]--;
            uint64_t c = 0;
            for (int k = 0; k < n; k++) {
                uint64_t sum = (uint64_t)u[j + k] + v[k] + c;
                u[j + k] = (uint32_t)sum;
                c = sum >> 32;
            }
            u[j + n] = (uint32_t)((uint64_t)u[j + n] + c);
        }
    }
    if (rem) {
        uint32_t r[4] = {0, 0, 0, 0};
        for (int i = 0; i < n; i++) r[i] = s ? (u[i] >> s) | (u[i + 1] << (32 - s)) : u[i];
        rem->lo = (uint64_t)r[0] | ((uint64_t)r[1] << 32);
        rem->hi = (uint64_t)r[2] | ((uint64_t)r[3] << 32);
    }
    lust_u128 out;
    out.lo = (uint64_t)q[0] | ((uint64_t)q[1] << 32);
    out.hi = (uint64_t)q[2] | ((uint64_t)q[3] << 32);
    return out;
})

/* 128 divided by a one-word divisor (b != 0); the format path. */
lust_u128 lust_u128_divmod64(lust_u128 a, uint64_t b, uint64_t *rem) LUST_BODY({
    lust_u128 d = {b, 0}, r;
    lust_u128 q = lust_u128_divmod(a, d, &r);
    if (rem) *rem = r.lo;
    return q;
})

lust_u128 lust_add_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    lust_u128 r = lust_u128_add(a, b);
    if (lust_u128_cmp(r, a) < 0) LUST_OVF("add");
    return r;
})
lust_u128 lust_sub_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    if (lust_u128_cmp(b, a) > 0) LUST_OVF("subtract");
    return lust_u128_sub(a, b);
})
lust_u128 lust_mul_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    lust_u128 r = lust_u128_mul(a, b);
    if ((a.lo || a.hi) && lust_u128_cmp(lust_u128_divmod(r, a, 0), b) != 0) LUST_OVF("multiply");
    return r;
})
lust_u128 lust_div_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    if (!b.lo && !b.hi) { lust_panic_cstr("attempt to divide by zero", loc); return b; }
    return lust_u128_divmod(a, b, 0);
})
lust_u128 lust_rem_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    if (!b.lo && !b.hi) { lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return b; }
    lust_u128 r;
    (void)lust_u128_divmod(a, b, &r);
    return r;
})

lust_u128 lust_i128_mag(lust_i128 a) LUST_BODY({
    lust_u128 u = lust_u128_from_i128(a);
    if ((int64_t)a.hi < 0) {
        lust_u128 z = {0, 0};
        return lust_u128_sub(z, u);
    }
    return u;
})

lust_i128 lust_add_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    lust_i128 r = lust_i128_add(a, b);
    if (((a.hi ^ r.hi) & (b.hi ^ r.hi)) >> 63) LUST_OVF("add");
    return r;
})
lust_i128 lust_sub_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    lust_i128 r = lust_i128_sub(a, b);
    if (((a.hi ^ b.hi) & (a.hi ^ r.hi)) >> 63) LUST_OVF("subtract");
    return r;
})
lust_i128 lust_neg_i128(lust_i128 a, lust_loc loc) LUST_BODY({
    if (a.lo == 0 && a.hi == 0x8000000000000000ull) LUST_OVF("negate");
    lust_i128 z = {0, 0};
    return lust_i128_sub(z, a);
})
lust_i128 lust_mul_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    if ((!a.lo && !a.hi) || (!b.lo && !b.hi)) { lust_i128 z = {0, 0}; return z; }
    if (a.lo == 0 && a.hi == 0x8000000000000000ull && b.lo == 0xFFFFFFFFFFFFFFFFull && b.hi == 0xFFFFFFFFFFFFFFFFull) LUST_OVF("multiply");
    if (b.lo == 0 && b.hi == 0x8000000000000000ull && a.lo == 0xFFFFFFFFFFFFFFFFull && a.hi == 0xFFFFFFFFFFFFFFFFull) LUST_OVF("multiply");
    lust_i128 r = lust_i128_mul(a, b);
    /* Divide back, as the i64 helper does; the -1 edges are handled above. */
    lust_u128 q = lust_u128_divmod(lust_i128_mag(r), lust_i128_mag(b), 0);
    if (lust_u128_cmp(q, lust_i128_mag(a)) != 0) LUST_OVF("multiply");
    /* |a*b| <= 2^127 now; +2^127 wraps to i128::MIN, so the sign tells. */
    if (((a.hi ^ b.hi ^ r.hi) >> 63) & 1) LUST_OVF("multiply");
    return r;
})
lust_i128 lust_div_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    if (!b.lo && !b.hi) { lust_panic_cstr("attempt to divide by zero", loc); return b; }
    if (a.lo == 0 && a.hi == 0x8000000000000000ull && b.lo == 0xFFFFFFFFFFFFFFFFull && b.hi == 0xFFFFFFFFFFFFFFFFull) LUST_OVF("divide");
    lust_u128 q = lust_u128_divmod(lust_i128_mag(a), lust_i128_mag(b), 0);
    if (((a.hi ^ b.hi) >> 63) & 1) {
        lust_u128 z = {0, 0};
        q = lust_u128_sub(z, q);
    }
    return lust_i128_from_u128(q);
})
lust_i128 lust_rem_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    if (!b.lo && !b.hi) { lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return b; }
    if (a.lo == 0 && a.hi == 0x8000000000000000ull && b.lo == 0xFFFFFFFFFFFFFFFFull && b.hi == 0xFFFFFFFFFFFFFFFFull) LUST_OVF("calculate the remainder");
    lust_u128 r;
    (void)lust_u128_divmod(lust_i128_mag(a), lust_i128_mag(b), &r);
    if ((int64_t)a.hi < 0) {
        lust_u128 z = {0, 0};
        r = lust_u128_sub(z, r);
    }
    return lust_i128_from_u128(r);
})

lust_i128 lust_abs_i128(lust_i128 a, lust_loc loc) LUST_BODY({ return (int64_t)a.hi < 0 ? lust_neg_i128(a, loc) : a; })
lust_u128 lust_pow_u128(lust_u128 a, uint32_t e, lust_loc loc) LUST_BODY({
    lust_u128 r = {1, 0};
    while (e) { if (e & 1) r = lust_mul_u128(r, a, loc); e >>= 1; if (e) a = lust_mul_u128(a, a, loc); }
    return r;
})
lust_i128 lust_pow_i128(lust_i128 a, uint32_t e, lust_loc loc) LUST_BODY({
    lust_i128 r = {1, 0};
    while (e) { if (e & 1) r = lust_mul_i128(r, a, loc); e >>= 1; if (e) a = lust_mul_i128(a, a, loc); }
    return r;
})
/* `abs` and `pow` with overflow checks off (release builds): they wrap. */
lust_i128 lust_wrapping_abs_i128(lust_i128 a) LUST_BODY({ lust_i128 z = {0, 0}; return (int64_t)a.hi < 0 ? lust_i128_sub(z, a) : a; })
lust_u128 lust_wrapping_pow_u128(lust_u128 a, uint32_t e) LUST_BODY({
    lust_u128 r = {1, 0};
    while (e) { if (e & 1) r = lust_u128_mul(r, a); e >>= 1; if (e) a = lust_u128_mul(a, a); }
    return r;
})
lust_i128 lust_wrapping_pow_i128(lust_i128 a, uint32_t e) LUST_BODY({
    lust_i128 r = {1, 0};
    while (e) { if (e & 1) r = lust_i128_mul(r, a); e >>= 1; if (e) a = lust_i128_mul(a, a); }
    return r;
})

/* Decimal format: split by 10^19, the largest power of ten in a word. */
void lust_fmt_u128(lust_String *out, lust_u128 v) LUST_BODY({
    if (!v.hi) { lust_fmt_u64(out, v.lo); return; }
    uint64_t chunks[3];
    int n = 0;
    while (v.lo || v.hi) {
        uint64_t r;
        v = lust_u128_divmod64(v, 10000000000000000000ull, &r);
        chunks[n++] = r;
    }
    lust_fmt_u64(out, chunks[--n]);
    char b[24];
    while (n > 0) {
        snprintf(b, sizeof b, "%019llu", (unsigned long long)chunks[--n]);
        lust_string_push_cstr(out, b);
    }
})
void lust_fmt_i128(lust_String *out, lust_i128 v) LUST_BODY({
    if ((int64_t)v.hi < 0) {
        lust_string_push_bytes(out, "-", 1);
        lust_fmt_u128(out, lust_i128_mag(v));
    } else {
        lust_fmt_u128(out, lust_u128_from_i128(v));
    }
})

/* Integer formatting with a format spec, as Rust renders it. `lo` and
   `hi` are the magnitude (already negated by the caller for decimal,
   raw two's-complement bits truncated to the type width for the radix
   modes, with `negative` clear). Modes: 0 decimal, 1 lower hex,
   2 upper hex, 3 octal, 4 binary. `align` is '<', '>', or '^', and
   0 for the numeric default (right). Precision is a minimum digit
   count; zero padding fills after the sign and radix prefix and is
   ignored when a precision is given, as in Rust. */
void lust_fmt_int_spec(lust_String *out, uint64_t lo, uint64_t hi, int negative, int mode, int plus, int alt, int zero_pad, uint32_t width, uint32_t fill, int align, int has_prec, uint32_t prec) LUST_BODY({
    static const char lo_digits[] = "0123456789abcdef";
    static const char up_digits[] = "0123456789ABCDEF";
    const char *digs = mode == 2 ? up_digits : lo_digits;
    uint64_t base = mode == 1 || mode == 2 ? 16 : mode == 3 ? 8 : mode == 4 ? 2 : 10;
    char rev[130];
    int nd = 0;
    lust_u128 v;
    v.lo = lo;
    v.hi = hi;
    if (!v.lo && !v.hi) {
        rev[nd++] = '0';
    } else {
        while (v.lo || v.hi) {
            uint64_t r;
            v = lust_u128_divmod64(v, base, &r);
            rev[nd++] = digs[r];
        }
    }
    const char *prefix = "";
    if (alt) prefix = mode == 1 ? "0x" : mode == 2 ? "0X" : mode == 3 ? "0o" : mode == 4 ? "0b" : "";
    uint64_t prefix_len = 0;
    while (prefix[prefix_len]) prefix_len++;
    int sign = negative ? '-' : plus ? '+' : 0;
    /* Precision is ignored for integers in Rust (it neither pads
       digits nor disables the zero flag). */
    uint32_t lead = 0;
    (void)has_prec; (void)prec;
    uint32_t total = (sign ? 1 : 0) + (uint32_t)prefix_len + lead + (uint32_t)nd;
    uint32_t zeros = 0;
    uint32_t left = 0, right = 0;
    if (zero_pad && total < width) {
        zeros = width - total;
        total = width;
    } else if (total < width) {
        uint32_t pad = width - total;
        if (align == '<') right = pad;
        else if (align == '^') { left = pad / 2; right = pad - left; }
        else left = pad;
    }
    uint32_t fill_cp = fill ? fill : ' ';
    for (uint32_t k = 0; k < left; k++) lust_string_push_char(out, fill_cp);
    if (sign) { char sc = (char)sign; lust_string_push_bytes(out, &sc, 1); }
    if (prefix_len) lust_string_push_bytes(out, prefix, prefix_len);
    for (uint32_t k = 0; k < zeros + lead; k++) lust_string_push_bytes(out, "0", 1);
    for (int k = nd - 1; k >= 0; k--) lust_string_push_bytes(out, &rev[k], 1);
    for (uint32_t k = 0; k < right; k++) lust_string_push_char(out, fill_cp);
})

/* The char count of a UTF-8 string view (non-continuation bytes). */
uint64_t lust_str_char_count(lust_str s) LUST_BODY({
    uint64_t n = 0;
    for (uint64_t i = 0; i < s.len; i++) if ((s.ptr[i] & 0xC0) != 0x80) n++;
    return n;
})

/* Appends `body` padded with `fill` to `width` chars: align '<'
   pads right, '^' centers (the larger half goes right, as in
   Rust), and anything else pads left. */
void lust_fmt_pad(lust_String *out, lust_str body, uint32_t width, uint32_t fill, int align) LUST_BODY({
    uint64_t count = lust_str_char_count(body);
    if (count >= width) { lust_string_push_str(out, body); return; }
    uint32_t pad = width - (uint32_t)count;
    uint32_t left = 0, right = 0;
    if (align == '<') right = pad;
    else if (align == '^') { left = pad / 2; right = pad - left; }
    else left = pad;
    uint32_t fill_cp = fill ? fill : ' ';
    for (uint32_t k = 0; k < left; k++) lust_string_push_char(out, fill_cp);
    lust_string_push_str(out, body);
    for (uint32_t k = 0; k < right; k++) lust_string_push_char(out, fill_cp);
})

/* Truncates a string to at most `chars` Unicode scalar values,
   cutting on a char boundary (a format precision for strings). */
void lust_str_trunc_chars(lust_String *s, uint32_t chars) LUST_BODY({
    uint32_t seen = 0;
    for (uint64_t i = 0; i < s->len; i++) {
        if ((s->ptr[i] & 0xC0) != 0x80) {
            if (seen == chars) { s->len = i; return; }
            seen++;
        }
    }
})

/* ---------- Vec insert/remove ---------- */

void lust_vec_insert_at(lust_Vec *v, uint64_t i, uint64_t elem, uint64_t align, lust_loc loc) LUST_BODY({
    if (i > v->len) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "insertion index (is ");
        lust_fmt_u64(&s, i);
        lust_string_push_cstr(&s, ") should be <= len (is ");
        lust_fmt_u64(&s, v->len);
        lust_string_push_cstr(&s, ")");
        lust_panic_dyn(&s, loc);
        return;
    }
    lust_vec_reserve(v, 1, elem, align);
    lust_copy_small((char *)v->ptr + (i + 1) * elem, (char *)v->ptr + i * elem, (v->len - i) * elem);
    v->len++;
})

void lust_vec_check_remove(lust_Vec *v, uint64_t i, lust_loc loc) LUST_BODY({
    if (i >= v->len) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "removal index (is ");
        lust_fmt_u64(&s, i);
        lust_string_push_cstr(&s, ") should be < len (is ");
        lust_fmt_u64(&s, v->len);
        lust_string_push_cstr(&s, ")");
        lust_panic_dyn(&s, loc);
    }
})

void lust_vec_remove_at(lust_Vec *v, uint64_t i, uint64_t elem) LUST_BODY({
    lust_copy_small((char *)v->ptr + i * elem, (char *)v->ptr + (i + 1) * elem, (v->len - i - 1) * elem);
    v->len--;
})

/* ---------- str ---------- */

uint8_t lust_str_starts_with(lust_str s, lust_str p) LUST_BODY({ return p.len <= s.len && (p.len == 0 || memcmp(s.ptr, p.ptr, p.len) == 0); })
uint8_t lust_str_ends_with(lust_str s, lust_str p) LUST_BODY({ return p.len <= s.len && (p.len == 0 || memcmp(s.ptr + s.len - p.len, p.ptr, p.len) == 0); })
/* str::contains and str::find with a &str pattern are lust_memmem (deps.c, declared here
   ahead of deps.h): its SSE2 path tries 16 starts at a time and gives the leftmost match, and
   0 for an empty pattern. */
uint64_t lust_memmem(const uint8_t *h, uint64_t hlen, const uint8_t *n, uint64_t nlen);
uint8_t lust_str_contains(lust_str s, lust_str p) LUST_BODY({ return lust_memmem(s.ptr, s.len, p.ptr, p.len) != UINT64_MAX; })

/* The byte index of the first (or last) match of `p` in `s`, or -1.
   An empty pattern matches at 0 for find and at s.len for rfind, as
   Rust's str::find and str::rfind do. A match of a UTF-8 pattern in
   a valid UTF-8 haystack always starts on a char boundary. */
int64_t lust_str_find(lust_str s, lust_str p) LUST_BODY({
    uint64_t i = lust_memmem(s.ptr, s.len, p.ptr, p.len);
    return i == UINT64_MAX ? -1 : (int64_t)i;
})
int64_t lust_str_rfind(lust_str s, lust_str p) LUST_BODY({
    if (p.len == 0) return (int64_t)s.len;
    if (p.len > s.len) return -1;
    for (uint64_t i = s.len - p.len;; i--) {
        if (s.ptr[i] == p.ptr[0] && memcmp(s.ptr + i, p.ptr, p.len) == 0) return (int64_t)i;
        if (i == 0) return -1;
    }
})

/* Unicode White_Space, as used by Rust's char::is_whitespace and the
   str trim methods. The table is generated (unicode_table.h). */
int lust_is_space(uint32_t c) LUST_BODY({ return LUST_UNI_IN(lust_uni_whitespace_ranges, c); })

/* Unicode char predicates over the generated range tables.
   is_alphanumeric is is_alphabetic || is_numeric: the generator
   asserts that identity for every scalar before it writes the table. */
int lust_char_is_alphabetic(uint32_t c) LUST_BODY({ return LUST_UNI_IN(lust_uni_alphabetic_ranges, c); })
int lust_char_is_numeric(uint32_t c) LUST_BODY({ return LUST_UNI_IN(lust_uni_numeric_ranges, c); })
int lust_char_is_alphanumeric(uint32_t c) LUST_BODY({
    return LUST_UNI_IN(lust_uni_alphabetic_ranges, c) || LUST_UNI_IN(lust_uni_numeric_ranges, c);
})
int lust_char_is_lowercase(uint32_t c) LUST_BODY({ return LUST_UNI_IN(lust_uni_lowercase_ranges, c); })
int lust_char_is_uppercase(uint32_t c) LUST_BODY({ return LUST_UNI_IN(lust_uni_uppercase_ranges, c); })
int lust_char_is_control(uint32_t c) LUST_BODY({ return LUST_UNI_IN(lust_uni_control_ranges, c); })

lust_str lust_str_trim_start(lust_str s) LUST_BODY({
    uint64_t a = 0;
    while (a < s.len) { uint64_t j = a; if (!lust_is_space(lust_utf8_next(s.ptr, &j))) break; a = j; }
    lust_str r; r.ptr = s.ptr + a; r.len = s.len - a;
    return r;
})

lust_str lust_str_trim_end(lust_str s) LUST_BODY({
    uint64_t b = s.len;
    while (b > 0) {
        uint64_t k = b - 1;
        while (k > 0 && (s.ptr[k] & 0xC0) == 0x80) k--;
        uint64_t j = k;
        if (!lust_is_space(lust_utf8_next(s.ptr, &j))) break;
        b = k;
    }
    lust_str r; r.ptr = s.ptr; r.len = b;
    return r;
})

/* Rust's `str::replace` for a `&str` pattern, capacities included:
   a one-byte pattern and one-byte `to` collect into exactly `s.len`;
   else the result starts at `s.len` when the pattern is no longer
   than `to` (0 otherwise) and grows by push_str of each piece
   (segment, `to`, ..., tail), with no exact or no-match fast path. */
/* `str::replacen(from, to, count)`: alloc's form, a String of capacity
   32 grown by `push_str`, the first `count` non-overlapping matches left
   to right replaced (an empty `from` matches at every char boundary,
   both ends included). */
lust_String lust_str_replacen(lust_str s, lust_str from, lust_str to, uint64_t count) LUST_BODY({
    lust_String r = lust_string_with_capacity(32);
    uint64_t last = 0, done = 0;
    if (from.len == 0) {
        uint64_t i = 0;
        while (done < count) {
            lust_string_push_bytes(&r, s.ptr + last, i - last);
            lust_string_push_str(&r, to);
            last = i;
            done++;
            if (i >= s.len) break;
            lust_utf8_next(s.ptr, &i);
        }
    } else {
        for (uint64_t i = 0; done < count && i + from.len <= s.len;) {
            if (s.ptr[i] == from.ptr[0] && memcmp(s.ptr + i, from.ptr, from.len) == 0) {
                lust_string_push_bytes(&r, s.ptr + last, i - last);
                lust_string_push_str(&r, to);
                i += from.len;
                last = i;
                done++;
            } else {
                i++;
            }
        }
    }
    lust_string_push_bytes(&r, s.ptr + last, s.len - last);
    return r;
})

lust_String lust_str_replace(lust_str s, lust_str from, lust_str to) LUST_BODY({
    if (from.len == 1 && to.len == 1) {
        lust_String r = lust_string_with_capacity(s.len);
        for (uint64_t i = 0; i < s.len; i++) r.ptr[i] = s.ptr[i] == from.ptr[0] ? to.ptr[0] : s.ptr[i];
        r.len = s.len;
        return r;
    }
    lust_String r = lust_string_with_capacity(from.len <= to.len ? s.len : 0);
    if (from.len == 0) {
        /* A match at every char boundary, both ends included: the
           pieces are `to`, then one char and `to` per char. */
        lust_string_push_str(&r, to);
        uint64_t i = 0;
        while (i < s.len) {
            uint64_t j = i;
            lust_utf8_next(s.ptr, &j);
            lust_string_push_bytes(&r, s.ptr + i, j - i);
            lust_string_push_str(&r, to);
            i = j;
        }
        return r;
    }
    uint64_t last = 0;
    for (uint64_t i = 0; i + from.len <= s.len;) {
        if (s.ptr[i] == from.ptr[0] && memcmp(s.ptr + i, from.ptr, from.len) == 0) {
            lust_string_push_bytes(&r, s.ptr + last, i - last);
            lust_string_push_str(&r, to);
            i += from.len;
            last = i;
        } else i++;
    }
    lust_string_push_bytes(&r, s.ptr + last, s.len - last);
    return r;
})

lust_String lust_str_repeat(lust_str s, uint64_t n, lust_loc loc) LUST_BODY({
    /* `checked_mul(n).expect(..)` in alloc's slice.rs, then RawVec's
       isize::MAX byte limit. */
    (void)loc;
    if (s.len && n > UINT64_MAX / s.len) { lust_panic_std("capacity overflow", "alloc/src/slice.rs:524:50"); return lust_string_new(); }
    uint64_t total = s.len * n;
    if (total > (uint64_t)9223372036854775807ull) { lust_vec_capacity_overflow(); return lust_string_new(); }
    lust_String r = lust_string_with_capacity(total);
    for (uint64_t i = 0; i < n; i++) { memcpy(r.ptr + r.len, s.ptr, s.len); r.len += s.len; }
    return r;
})

/* `<[T]>::repeat(n)` for `T: Copy` (alloc's slice.rs), which `str::repeat`
   calls: the same `checked_mul` panic, then RawVec's capacity limit. */
lust_Vec lust_slice_repeat(const void *p, uint64_t len, uint64_t n, uint64_t elem, uint64_t align) LUST_BODY({
    if (len && n > UINT64_MAX / len) { lust_panic_std("capacity overflow", "alloc/src/slice.rs:524:50"); return lust_vec_with_capacity(0, elem, align); }
    lust_Vec r = lust_vec_with_capacity(len * n, elem, align);
    if (elem && len) for (uint64_t i = 0; i < n; i++) memcpy((char *)r.ptr + i * len * elem, p, len * elem);
    r.len = len * n;
    return r;
})

void lust_string_shrink_to(lust_String *s, uint64_t min_cap) LUST_BODY({
    uint64_t target = min_cap > s->len ? min_cap : s->len;
    if (s->cap <= target) return;
    if (!target) {
        free(s->ptr);
        s->ptr = (uint8_t *)(uintptr_t)1;
        s->cap = 0;
        return;
    }
    s->ptr = lust_realloc(s->ptr, s->cap, 1, target);
    s->cap = target;
})

/* The byte offset where the char at byte `end` starts searching
   backward; `end` is one past that char and must be > 0. */
static uint64_t lust_str_prev_start(const uint8_t *p, uint64_t end) {
    uint64_t k = end - 1;
    while (k > 0 && (p[k] & 0xC0) == 0x80) k--;
    return k;
}

uint32_t lust_string_pop(lust_String *s) LUST_BODY({
    uint64_t k = lust_str_prev_start(s->ptr, s->len);
    uint64_t j = k;
    uint32_t c = lust_utf8_next(s->ptr, &j);
    s->len = k;
    return c;
})

/* Rust's `assert!(self.is_char_boundary(<what>))` in String methods. */
static void lust_string_check_boundary(lust_String *s, uint64_t idx, const char *what, lust_loc loc) {
    if (idx > s->len || (idx < s->len && (s->ptr[idx] & 0xC0) == 0x80)) {
        lust_String m = lust_string_new();
        lust_string_push_cstr(&m, "assertion failed: self.is_char_boundary(");
        lust_string_push_cstr(&m, what);
        lust_string_push_cstr(&m, ")");
        lust_panic(&m, loc);
    }
}

/* String::remove slices `self[idx..]` first, so it panics as that slice does. */
uint32_t lust_string_remove(lust_String *s, uint64_t idx, lust_loc loc) LUST_BODY({
    (void)lust_str_range(s->ptr, idx, s->len, 0, s->len, loc);
    if (lust_unwind_mode && lust_unw_mine()) return 0;
    if (idx == s->len) { lust_panic_cstr("cannot remove a char from the end of a string", loc); return 0; }
    uint64_t j = idx;
    uint32_t c = lust_utf8_next(s->ptr, &j);
    memmove(s->ptr + idx, s->ptr + j, s->len - j);
    s->len -= j - idx;
    return c;
})

void lust_string_insert_bytes(lust_String *s, uint64_t idx, const uint8_t *p, uint64_t n, lust_loc loc) LUST_BODY({
    lust_string_check_boundary(s, idx, "idx", loc);
    if (lust_unwind_mode && lust_unw_mine()) return;
    /* Copy the inserted bytes first: they may view this String. */
    uint8_t small[4];
    uint8_t *tmp = small;
    if (n > sizeof small) { tmp = lust_alloc(n, 1); }
    memcpy(tmp, p, n);
    lust_string_reserve(s, n);
    memmove(s->ptr + idx + n, s->ptr + idx, s->len - idx);
    memcpy(s->ptr + idx, tmp, n);
    if (tmp != small) free(tmp);
    s->len += n;
})

void lust_string_insert_char(lust_String *s, uint64_t idx, uint32_t c, lust_loc loc) LUST_BODY({
    uint8_t b[4];
    int n;
    if (c < 0x80) { b[0] = c; n = 1; }
    else if (c < 0x800) { b[0] = 0xC0 | (c >> 6); b[1] = 0x80 | (c & 0x3F); n = 2; }
    else if (c < 0x10000) { b[0] = 0xE0 | (c >> 12); b[1] = 0x80 | ((c >> 6) & 0x3F); b[2] = 0x80 | (c & 0x3F); n = 3; }
    else { b[0] = 0xF0 | (c >> 18); b[1] = 0x80 | ((c >> 12) & 0x3F); b[2] = 0x80 | ((c >> 6) & 0x3F); b[3] = 0x80 | (c & 0x3F); n = 4; }
    lust_string_insert_bytes(s, idx, b, (uint64_t)n, loc);
})

void lust_string_truncate(lust_String *s, uint64_t n, lust_loc loc) LUST_BODY({
    if (n < s->len) {
        lust_string_check_boundary(s, n, "new_len", loc);
        if (lust_unwind_mode && lust_unw_mine()) return;
        s->len = n;
    }
})

lust_String lust_string_split_off(lust_String *s, uint64_t at, lust_loc loc) LUST_BODY({
    lust_string_check_boundary(s, at, "at", loc);
    if (lust_unwind_mode && lust_unw_mine()) return lust_string_new();
    lust_String r = lust_string_with_capacity(s->len - at);
    memcpy(r.ptr, s->ptr + at, s->len - at);
    r.len = s->len - at;
    s->len = at;
    return r;
})

lust_str lust_str_trim(lust_str s) LUST_BODY({
    uint64_t a = 0, b = s.len;
    while (a < b) { uint64_t j = a; if (!lust_is_space(lust_utf8_next(s.ptr, &j))) break; a = j; }
    while (b > a) {
        uint64_t k = b - 1;
        while (k > a && (s.ptr[k] & 0xC0) == 0x80) k--;
        uint64_t j = k;
        if (!lust_is_space(lust_utf8_next(s.ptr, &j))) break;
        b = k;
    }
    lust_str r; r.ptr = s.ptr + a; r.len = b - a;
    return r;
})

/* ASCII case mapping. Non-ASCII characters are copied unchanged (Rust maps them too). */
lust_String lust_str_ascii_case(lust_str s, int upper) LUST_BODY({
    lust_String r = lust_string_from(s);
    for (uint64_t i = 0; i < r.len; i++) {
        uint8_t c = r.ptr[i];
        if (upper && c >= 'a' && c <= 'z') r.ptr[i] = c - 32;
        if (!upper && c >= 'A' && c <= 'Z') r.ptr[i] = c + 32;
    }
    return r;
})

typedef struct { lust_str s; uint64_t pos; } lust_Chars;
lust_Chars lust_chars(lust_str s) LUST_BODY({ lust_Chars c; c.s = s; c.pos = 0; return c; })
uint64_t lust_chars_count(lust_Chars c) LUST_BODY({
    uint64_t n = 0;
    while (c.pos < c.s.len) { lust_utf8_next(c.s.ptr, &c.pos); n++; }
    return n;
})
/* The char that ends at `*end` (`Chars::next_back`): back over the
   continuation bytes, decode forward, and leave `*end` at its start. */
uint32_t lust_utf8_prev(const uint8_t *p, uint64_t *end) LUST_BODY({
    uint64_t i = *end - 1;
    while (i > 0 && (p[i] & 0xC0) == 0x80) i--;
    uint64_t j = i;
    uint32_t c = lust_utf8_next(p, &j);
    *end = i;
    return c;
})

/* The str split family (W-STD-B): std's SplitInternal and SplitNInternal
   over its searchers (CharSearcher, MultiCharEqSearcher for char sets and
   predicates, StrSearcher with its EmptyNeedle form). `lust_split` is the
   common start of the generated iterator struct (ty/iter.rs StrSplit):
   the haystack, the part not yet yielded (start..end), the searcher's
   front and back positions, flags, and a SplitN count. `lust_pat` names
   the pattern for one step. Modes follow ty/iter.rs SplitMode. */
typedef struct { lust_str hay; uint64_t start, end, fpos, bpos, flags, count; } lust_split;
typedef struct {
    uint8_t kind;
    uint32_t ch;
    lust_str needle;
    const uint32_t *set;
    uint64_t n;
    uint8_t (*pred)(void *, uint32_t);
    void *env;
} lust_pat;
enum { LUST_PAT_CHAR, LUST_PAT_STR, LUST_PAT_SET, LUST_PAT_PRED, LUST_PAT_SPACE, LUST_PAT_ASCII_SPACE };
enum { LUST_SPLIT_FINISHED = 1, LUST_SPLIT_TRAILING = 2, LUST_SPLIT_MATCH_FW = 4, LUST_SPLIT_MATCH_BW = 8, LUST_SPLIT_EMPTY_DONE = 16 };

/* One char against a char-at-a-time pattern (each predicate call once,
   in scan order, as MultiCharEqSearcher). */
int lust_pat_hit(const lust_pat *p, uint32_t c) LUST_BODY({
    switch (p->kind) {
    case LUST_PAT_CHAR: return c == p->ch;
    case LUST_PAT_SET:
        for (uint64_t i = 0; i < p->n; i++)
            if (p->set[i] == c) return 1;
        return 0;
    case LUST_PAT_PRED: return p->pred(p->env, c) != 0;
    case LUST_PAT_SPACE: return lust_is_space(c);
    default: return c == ' ' || c == '\t' || c == '\n' || c == 0x0C || c == '\r';
    }
})

/* next_match: the next match in fpos..bpos from the front (the empty
   needle walks from fpos to the haystack's end, as std). */
int lust_split_match_fw(lust_split *s, const lust_pat *p, uint64_t *a, uint64_t *b) LUST_BODY({
    const uint8_t *h = s->hay.ptr;
    if (p->kind == LUST_PAT_STR) {
        uint64_t m = p->needle.len;
        if (m == 0) {
            for (;;) {
                if (s->flags & LUST_SPLIT_EMPTY_DONE) return 0;
                int hit = (s->flags & LUST_SPLIT_MATCH_FW) != 0;
                s->flags ^= LUST_SPLIT_MATCH_FW;
                uint64_t pos = s->fpos;
                if (hit) { *a = pos; *b = pos; return 1; }
                if (pos >= s->hay.len) { s->flags |= LUST_SPLIT_EMPTY_DONE; return 0; }
                lust_utf8_next(h, &s->fpos);
            }
        }
        for (uint64_t i = s->fpos; i + m <= s->bpos; i++) {
            if (memcmp(h + i, p->needle.ptr, m) == 0) { *a = i; *b = i + m; s->fpos = i + m; return 1; }
        }
        s->fpos = s->bpos;
        return 0;
    }
    while (s->fpos < s->bpos) {
        uint64_t i = s->fpos;
        uint32_t c = lust_utf8_next(h, &s->fpos);
        if (lust_pat_hit(p, c)) { *a = i; *b = s->fpos; return 1; }
    }
    return 0;
})

/* next_match_back: the last match in fpos..bpos (the empty needle walks
   from bpos to the haystack's start, as std). */
int lust_split_match_bw(lust_split *s, const lust_pat *p, uint64_t *a, uint64_t *b) LUST_BODY({
    const uint8_t *h = s->hay.ptr;
    if (p->kind == LUST_PAT_STR) {
        uint64_t m = p->needle.len;
        if (m == 0) {
            for (;;) {
                if (s->flags & LUST_SPLIT_EMPTY_DONE) return 0;
                int hit = (s->flags & LUST_SPLIT_MATCH_BW) != 0;
                s->flags ^= LUST_SPLIT_MATCH_BW;
                uint64_t end = s->bpos;
                if (hit) { *a = end; *b = end; return 1; }
                if (end == 0) { s->flags |= LUST_SPLIT_EMPTY_DONE; return 0; }
                lust_utf8_prev(h, &s->bpos);
            }
        }
        for (uint64_t j = s->bpos; j >= s->fpos + m && j >= m; j--) {
            if (memcmp(h + j - m, p->needle.ptr, m) == 0) { *a = j - m; *b = j; s->bpos = j - m; return 1; }
            if (j == 0) break;
        }
        s->bpos = s->fpos;
        return 0;
    }
    while (s->bpos > s->fpos) {
        uint64_t j = s->bpos;
        uint32_t c = lust_utf8_prev(h, &s->bpos);
        if (lust_pat_hit(p, c)) { *a = s->bpos; *b = j; return 1; }
    }
    return 0;
})

lust_str lust_split_sub(lust_str h, uint64_t a, uint64_t b) LUST_BODY({ lust_str r; r.ptr = h.ptr + a; r.len = b - a; return r; })

/* SplitInternal::get_end. */
int lust_split_get_end(lust_split *s, lust_str *out) LUST_BODY({
    if (s->flags & LUST_SPLIT_FINISHED) return 0;
    s->flags |= LUST_SPLIT_FINISHED;
    if ((s->flags & LUST_SPLIT_TRAILING) || s->end > s->start) { *out = lust_split_sub(s->hay, s->start, s->end); return 1; }
    return 0;
})

/* SplitInternal::next, and next_inclusive when `incl`. */
int lust_split_fw(lust_split *s, const lust_pat *p, int incl, lust_str *out) LUST_BODY({
    if (s->flags & LUST_SPLIT_FINISHED) return 0;
    uint64_t a, b;
    if (lust_split_match_fw(s, p, &a, &b)) {
        *out = lust_split_sub(s->hay, s->start, incl ? b : a);
        s->start = b;
        return 1;
    }
    return lust_split_get_end(s, out);
})

/* SplitInternal::next_back, and next_back_inclusive when `incl`. */
int lust_split_bw(lust_split *s, const lust_pat *p, int incl, lust_str *out) LUST_BODY({
    if (s->flags & LUST_SPLIT_FINISHED) return 0;
    if (!(s->flags & LUST_SPLIT_TRAILING)) {
        s->flags |= LUST_SPLIT_TRAILING;
        lust_str e;
        if (lust_split_bw(s, p, incl, &e) && e.len > 0) { *out = e; return 1; }
        if (s->flags & LUST_SPLIT_FINISHED) return 0;
    }
    uint64_t a, b;
    if (lust_split_match_bw(s, p, &a, &b)) {
        *out = lust_split_sub(s->hay, b, s->end);
        s->end = incl ? b : a;
        return 1;
    }
    s->flags |= LUST_SPLIT_FINISHED;
    *out = lust_split_sub(s->hay, s->start, s->end);
    return 1;
})

/* One `next` (`next_back` when `back`) of a split iterator in `mode`. */
int lust_split_step(lust_split *s, const lust_pat *p, uint8_t mode, int back, lust_str *out) LUST_BODY({
    switch (mode) {
    case 0: case 2: return back ? lust_split_bw(s, p, 0, out) : lust_split_fw(s, p, 0, out);
    case 1: case 3: return back ? lust_split_fw(s, p, 0, out) : lust_split_bw(s, p, 0, out);
    case 4: case 5:
        if (s->count == 0) return 0;
        if (s->count == 1) { s->count = 0; return lust_split_get_end(s, out); }
        s->count--;
        return mode == 4 ? lust_split_fw(s, p, 0, out) : lust_split_bw(s, p, 0, out);
    case 6: return back ? lust_split_bw(s, p, 1, out) : lust_split_fw(s, p, 1, out);
    case 7: case 8:
        for (;;) {
            int got = back ? lust_split_bw(s, p, 0, out) : lust_split_fw(s, p, 0, out);
            if (!got) return 0;
            if (out->len > 0) return 1;
        }
    default: {
        int got = back ? lust_split_bw(s, p, 1, out) : lust_split_fw(s, p, 1, out);
        if (got && out->len > 0 && out->ptr[out->len - 1] == '\n') {
            out->len--;
            if (out->len > 0 && out->ptr[out->len - 1] == '\r') out->len--;
        }
        return got;
    }
    }
})

/* `split_ascii_whitespace`'s upper bound (slice::Split's, through the
   filter): 0 once finished, else the bytes left plus one. */
uint64_t lust_split_upper(const lust_split *s) LUST_BODY({ return (s->flags & LUST_SPLIT_FINISHED) ? 0 : s->end - s->start + 1; })

/* `split_once` (`rsplit_once` when `back`): the first (last) match. */
int lust_str_split_once(lust_str hay, const lust_pat *p, int back, lust_str *a, lust_str *b) LUST_BODY({
    lust_split s;
    s.hay = hay; s.start = 0; s.end = hay.len; s.fpos = 0; s.bpos = hay.len;
    s.flags = LUST_SPLIT_MATCH_FW | LUST_SPLIT_MATCH_BW; s.count = 0;
    uint64_t x, y;
    if (!(back ? lust_split_match_bw(&s, p, &x, &y) : lust_split_match_fw(&s, p, &x, &y))) return 0;
    *a = lust_split_sub(hay, 0, x);
    *b = lust_split_sub(hay, y, hay.len);
    return 1;
})

/* The str search and trim methods over a `lust_pat` (tf-str), on the
   split family's searchers so predicate calls run once per char in
   scan order, as std's do. A char-at-a-time pattern matches single
   chars; a string needle matches its bytes (only on char boundaries,
   as both texts are valid UTF-8). */

/* One match of `p` in `hay`, the first (or last, when `back`). */
int lust_pat_match(lust_str hay, const lust_pat *p, int back, uint64_t *a, uint64_t *b) LUST_BODY({
    lust_split s;
    s.hay = hay; s.start = 0; s.end = hay.len; s.fpos = 0; s.bpos = hay.len;
    s.flags = LUST_SPLIT_MATCH_FW | LUST_SPLIT_MATCH_BW; s.count = 0;
    return back ? lust_split_match_bw(&s, p, a, b) : lust_split_match_fw(&s, p, a, b);
})

/* A match at the start of `hay`, with its end: the needle as a
   prefix, or the first char against a char-at-a-time pattern. */
int lust_pat_prefix(lust_str hay, const lust_pat *p, uint64_t *end) LUST_BODY({
    if (p->kind == LUST_PAT_STR) {
        *end = p->needle.len;
        return p->needle.len <= hay.len && (p->needle.len == 0 || memcmp(hay.ptr, p->needle.ptr, p->needle.len) == 0);
    }
    if (hay.len == 0) return 0;
    uint64_t j = 0;
    uint32_t c = lust_utf8_next(hay.ptr, &j);
    if (!lust_pat_hit(p, c)) return 0;
    *end = j;
    return 1;
})

/* A match at the end of `hay`, with its start. */
int lust_pat_suffix(lust_str hay, const lust_pat *p, uint64_t *start) LUST_BODY({
    if (p->kind == LUST_PAT_STR) {
        if (p->needle.len > hay.len) return 0;
        *start = hay.len - p->needle.len;
        return p->needle.len == 0 || memcmp(hay.ptr + *start, p->needle.ptr, p->needle.len) == 0;
    }
    if (hay.len == 0) return 0;
    uint64_t e = hay.len;
    uint32_t c = lust_utf8_prev(hay.ptr, &e);
    if (!lust_pat_hit(p, c)) return 0;
    *start = e;
    return 1;
})

/* `trim_start_matches`: for a needle, strip it as a prefix while it
   is one (an empty needle changes nothing); else strip matching
   chars from the front. */
lust_str lust_pat_trim_start(lust_str hay, const lust_pat *p) LUST_BODY({
    uint64_t a = 0;
    if (p->kind == LUST_PAT_STR) {
        uint64_t m = p->needle.len;
        while (m > 0 && a + m <= hay.len && memcmp(hay.ptr + a, p->needle.ptr, m) == 0) a += m;
    } else {
        while (a < hay.len) {
            uint64_t j = a;
            if (!lust_pat_hit(p, lust_utf8_next(hay.ptr, &j))) break;
            a = j;
        }
    }
    return lust_split_sub(hay, a, hay.len);
})

/* `trim_end_matches`, from the back. */
lust_str lust_pat_trim_end(lust_str hay, const lust_pat *p) LUST_BODY({
    uint64_t b = hay.len;
    if (p->kind == LUST_PAT_STR) {
        uint64_t m = p->needle.len;
        while (m > 0 && b >= m && memcmp(hay.ptr + b - m, p->needle.ptr, m) == 0) b -= m;
    } else {
        while (b > 0) {
            uint64_t e = b;
            if (!lust_pat_hit(p, lust_utf8_prev(hay.ptr, &e))) break;
            b = e;
        }
    }
    return lust_split_sub(hay, 0, b);
})

/* One `next` (`next_back` when `back`) of a matches iterator: the
   match's start index and text. The state is a `lust_split` whose
   start and end stay 0 and hay.len. */
int lust_matches_step(lust_split *s, const lust_pat *p, int back, uint64_t *idx, lust_str *out) LUST_BODY({
    uint64_t a, b;
    if (!(back ? lust_split_match_bw(s, p, &a, &b) : lust_split_match_fw(s, p, &a, &b))) return 0;
    *idx = a;
    *out = lust_split_sub(s->hay, a, b);
    return 1;
})

/* `str::replace` / `replacen` over a char set or predicate pattern:
   alloc's loop over `match_indices(pat).take(count)` into a String of
   capacity `cap` (0 for `replace`, whose pattern has no UTF-8 form; 32
   for `replacen`). The searcher stops after `count` matches, so a
   predicate sees no char past the last replaced match. */
lust_String lust_pat_replacen(lust_str hay, const lust_pat *p, lust_str to, uint64_t count, uint64_t cap) LUST_BODY({
    lust_String r = lust_string_with_capacity(cap);
    lust_split s;
    s.hay = hay; s.start = 0; s.end = hay.len; s.fpos = 0; s.bpos = hay.len;
    s.flags = LUST_SPLIT_MATCH_FW | LUST_SPLIT_MATCH_BW; s.count = 0;
    uint64_t last = 0, done = 0, a, b;
    while (done < count && lust_split_match_fw(&s, p, &a, &b)) {
        lust_string_push_bytes(&r, hay.ptr + last, a - last);
        lust_string_push_str(&r, to);
        last = b;
        done++;
    }
    lust_string_push_bytes(&r, hay.ptr + last, hay.len - last);
    return r;
})

/* The primitive `FromStr` parsers (tf-str), core's semantics.
   Int kinds follow `IntErrorKind` (Empty 0, InvalidDigit 1,
   PosOverflow 2, NegOverflow 3): core's `from_str_radix` at radix
   10 checks each digit, then the checked multiply and add, in
   order, so an overflow ahead of a bad digit reports the overflow.
   The magnitude is accumulated in two words, so 128-bit targets
   take the same path. `from_str_radix` (R26) runs it at any radix in
   2..=36 (the caller checks the range); a letter digit is either case. */
int lust_parse_int_radix(lust_str s, uint32_t radix, int is_signed, int bits, uint64_t *lo, uint64_t *hi, int *kind) LUST_BODY({
    *lo = 0; *hi = 0;
    if (s.len == 0) { *kind = 0; return 0; }
    uint64_t i = 0;
    int neg = 0;
    if (s.ptr[0] == '+') {
        i = 1;
    } else if (s.ptr[0] == '-' && is_signed) {
        neg = 1;
        i = 1;
    }
    if (i >= s.len) { *kind = 1; return 0; }
    /* The magnitude limit: the type's max, or its min's magnitude. */
    uint64_t lim_lo, lim_hi;
    if (bits >= 128) {
        lim_hi = is_signed ? 0x7fffffffffffffffULL : 0xffffffffffffffffULL;
        lim_lo = 0xffffffffffffffffULL;
        if (is_signed && neg) { lim_hi = 0x8000000000000000ULL; lim_lo = 0; }
    } else if (bits == 64) {
        lim_hi = 0;
        lim_lo = is_signed ? (neg ? 0x8000000000000000ULL : 0x7fffffffffffffffULL) : 0xffffffffffffffffULL;
    } else {
        lim_hi = 0;
        uint64_t top = bits == 32 ? 0xffffffffULL : (bits == 16 ? 0xffffULL : 0xffULL);
        lim_lo = is_signed ? (neg ? (top / 2 + 1) : top / 2) : top;
    }
    uint64_t rlo = 0, rhi = 0;
    for (; i < s.len; i++) {
        uint8_t ch = s.ptr[i];
        uint64_t d = ch >= '0' && ch <= '9' ? (uint64_t)(ch - '0')
            : (ch | 32) >= 'a' && (ch | 32) <= 'z' ? (uint64_t)((ch | 32) - 'a' + 10) : 99;
        if (d >= radix) { *kind = 1; return 0; }
        /* r = r * radix + d, checked against the limit. A high word
           that would wrap past two words is past every limit. */
        uint64_t lo10 = (rlo & 0xffffffffULL) * radix;
        uint64_t hi10 = (rlo >> 32) * radix + (lo10 >> 32);
        if (rhi > (0xffffffffffffffffULL - (hi10 >> 32)) / radix) { *kind = neg ? 3 : 2; return 0; }
        uint64_t nlo = (lo10 & 0xffffffffULL) | ((hi10 & 0xffffffffULL) << 32);
        uint64_t nhi = (hi10 >> 32) + rhi * radix;
        nlo += d;
        if (nlo < d) {
            if (nhi == 0xffffffffffffffffULL) { *kind = neg ? 3 : 2; return 0; }
            nhi += 1;
        }
        if (nhi > lim_hi || (nhi == lim_hi && nlo > lim_lo)) { *kind = neg ? 3 : 2; return 0; }
        rlo = nlo; rhi = nhi;
    }
    if (neg) {
        /* Two's complement negation in the target width. */
        if (bits >= 128) {
            *lo = ~rlo + 1;
            *hi = ~rhi + (*lo == 0);
        } else if (bits == 64) {
            *lo = 0 - rlo; *hi = 0;
        } else {
            uint64_t mask = bits == 32 ? 0xffffffffULL : (bits == 16 ? 0xffffULL : 0xffULL);
            *lo = (0 - rlo) & mask; *hi = 0;
        }
    } else {
        *lo = rlo; *hi = rhi;
    }
    *kind = 0;
    return 1;
})

int lust_parse_int(lust_str s, int is_signed, int bits, uint64_t *lo, uint64_t *hi, int *kind) LUST_BODY({
    return lust_parse_int_radix(s, 10, is_signed, bits, lo, hi, kind);
})

/* core's `from_str_radix` radix check: a panic before any parsing. */
void lust_radix_check(uint32_t radix, lust_loc loc) LUST_BODY({
    if (radix >= 2 && radix <= 36) return;
    lust_String m = lust_string_new();
    lust_string_push_cstr(&m, "from_ascii_bytes_radix: radix must lie in the range `[2, 36]` - found ");
    lust_fmt_u64(&m, radix);
    lust_panic_dyn(&m, loc);
})

/* The float parsers of float.c (Rust's grammar, correctly
   rounded), declared in float.h below; 1 is empty, 2 is invalid. */
int lust_parse_f64(lust_str s, double *out);
int lust_parse_f32(lust_str s, float *out);

/* `f64::from_str` (tf-str): over the float core's parser, with
   core's error kinds (0 Empty, 1 Invalid). */
int lust_str_parse_f64(lust_str s, double *out, int *kind) LUST_BODY({
    int rc = lust_parse_f64(s, out);
    *kind = rc == 1 ? 0 : 1;
    return rc == 0;
})

int lust_str_parse_f32(lust_str s, float *out, int *kind) LUST_BODY({
    int rc = lust_parse_f32(s, out);
    *kind = rc == 1 ? 0 : 1;
    return rc == 0;
})

/* `bool::from_str`: exactly `true` or `false`. */
int lust_parse_bool(lust_str s, uint8_t *out) LUST_BODY({
    if (s.len == 4 && memcmp(s.ptr, "true", 4) == 0) { *out = 1; return 1; }
    if (s.len == 5 && memcmp(s.ptr, "false", 5) == 0) { *out = 0; return 1; }
    return 0;
})

/* `char::from_str`: exactly one char (kind: 0 EmptyString,
   1 TooManyChars). */
int lust_parse_char(lust_str s, uint32_t *out, int *kind) LUST_BODY({
    if (s.len == 0) { *kind = 0; return 0; }
    uint64_t j = 0;
    uint32_t c = lust_utf8_next(s.ptr, &j);
    if (j != s.len) { *kind = 1; return 0; }
    *out = c;
    *kind = 0;
    return 1;
})

/* `String::from_utf16_lossy` (tf-str): `char::decode_utf16` over
   the units collected into a String, as alloc runs it. The collect
   starts at the decoder's size-hint lower bound, `(units + 1) / 2`
   rounded as core counts it (an even count halves exactly), then
   pushes one char at a time, with U+FFFD for each unpaired
   surrogate, so capacities grow as std's do. */
lust_String lust_string_from_utf16_lossy(const uint16_t *v, uint64_t n) LUST_BODY({
    lust_String s = lust_string_new();
    lust_string_reserve(&s, (n + 1) / 2);
    uint64_t i = 0;
    while (i < n) {
        uint16_t u = v[i++];
        uint32_t c;
        if (u >= 0xD800 && u < 0xDC00) {
            if (i < n && v[i] >= 0xDC00 && v[i] < 0xE000) {
                c = 0x10000 + (((uint32_t)(u - 0xD800) << 10) | (uint32_t)(v[i] - 0xDC00));
                i++;
            } else {
                c = 0xFFFD;
            }
        } else if (u >= 0xDC00 && u < 0xE000) {
            c = 0xFFFD;
        } else {
            c = u;
        }
        lust_string_push_char(&s, c);
    }
    return s;
})

/* str::to_uppercase and str::to_lowercase as Rust 1.99 runs them
   (W-STD-B): the ASCII prefix byte by byte into a String with the str's
   length as capacity (`convert_while_ascii`), then each char through
   rustc-generated tables (one to three chars, pushed one by one), and in
   to_lowercase 'Σ' by the final-sigma rule. The tables are in the runtime
   unit only (`runtime_source`). */
#include "case_tables.h"
static int lust_case_in(const uint32_t (*t)[2], uint64_t n, uint32_t c) LUST_BODY({
    uint64_t lo = 0, hi = n;
    while (lo < hi) {
        uint64_t m = lo + (hi - lo) / 2;
        if (c < t[m][0]) hi = m;
        else if (c > t[m][1]) lo = m + 1;
        else return 1;
    }
    return 0;
})
static const uint32_t *lust_case_map(const uint32_t (*t)[4], uint64_t n, uint32_t c) LUST_BODY({
    uint64_t lo = 0, hi = n;
    while (lo < hi) {
        uint64_t m = lo + (hi - lo) / 2;
        if (c < t[m][0]) hi = m;
        else if (c > t[m][0]) lo = m + 1;
        else return &t[m][1];
    }
    return 0;
})
/* `case_ignorable_then_cased` over the chars before byte `i` (backward)
   or from byte `i` on (forward). */
static int lust_ci_then_cased(lust_str s, uint64_t i, int back) LUST_BODY({
    for (;;) {
        uint32_t c;
        if (back) {
            if (i == 0) return 0;
            c = lust_utf8_prev(s.ptr, &i);
        } else {
            if (i >= s.len) return 0;
            c = lust_utf8_next(s.ptr, &i);
        }
        if (lust_case_in(lust_case_ignorable, sizeof lust_case_ignorable / sizeof lust_case_ignorable[0], c)) continue;
        return c == 0x3A3 || lust_case_in(lust_cased, sizeof lust_cased / sizeof lust_cased[0], c);
    }
})
lust_String lust_str_case(lust_str s, int upper) LUST_BODY({
    lust_String r = lust_string_with_capacity(s.len);
    uint64_t i = 0;
    while (i < s.len && s.ptr[i] < 0x80) {
        uint8_t c = s.ptr[i];
        if (upper && c >= 'a' && c <= 'z') c -= 32;
        if (!upper && c >= 'A' && c <= 'Z') c += 32;
        r.ptr[i] = c;
        i++;
    }
    r.len = i;
    while (i < s.len) {
        uint64_t at = i;
        uint32_t c = lust_utf8_next(s.ptr, &i);
        if (!upper && c == 0x3A3) {
            int fin = lust_ci_then_cased(s, at, 1) && !lust_ci_then_cased(s, at + 2, 0);
            lust_string_push_char(&r, fin ? 0x3C2 : 0x3C3);
            continue;
        }
        const uint32_t *m = upper ? lust_case_map(lust_upper_map, sizeof lust_upper_map / sizeof lust_upper_map[0], c)
                                  : lust_case_map(lust_lower_map, sizeof lust_lower_map / sizeof lust_lower_map[0], c);
        if (!m) { lust_string_push_char(&r, c); continue; }
        lust_string_push_char(&r, m[0]);
        if (m[1]) lust_string_push_char(&r, m[1]);
        if (m[2]) lust_string_push_char(&r, m[2]);
    }
    return r;
})

/* `char::to_lowercase` and `char::to_uppercase` for one char, as the
   `char_case` intrinsic returns it: the mapped code points (one to
   three, 21 bits each) in `lo`, their count in `hi`. No final-sigma
   rule: that is `str::to_lowercase` only. */
lust_u128 lust_char_case(uint32_t c, uint8_t upper) LUST_BODY({
    const uint32_t *m = upper ? lust_case_map(lust_upper_map, sizeof lust_upper_map / sizeof lust_upper_map[0], c)
                              : lust_case_map(lust_lower_map, sizeof lust_lower_map / sizeof lust_lower_map[0], c);
    uint32_t o0 = c, o1 = 0, o2 = 0;
    uint64_t n = 1;
    if (m) {
        o0 = m[0]; o1 = m[1]; o2 = m[2];
        n = o2 ? 3 : o1 ? 2 : 1;
    }
    lust_u128 r;
    r.lo = (uint64_t)o0 | ((uint64_t)o1 << 21) | ((uint64_t)o2 << 42);
    r.hi = n;
    return r;
})

/* The `encode_utf8: need ...` panic text of core (char/methods.rs),
   shared by the two encode helpers below. */
static void lust_encode_panic(const char *what, uint64_t need, uint32_t c, uint64_t have, lust_loc loc) LUST_BODY({
    char hex[16];
    int hn = 0;
    uint32_t v = c;
    if (v == 0) hex[hn++] = '0';
    char rev[16];
    int rn = 0;
    while (v) { rev[rn++] = "0123456789ABCDEF"[v & 15]; v >>= 4; }
    while (rn + hn < 4) hex[hn++] = '0';
    while (rn) hex[hn++] = rev[--rn];
    hex[hn] = 0;
    lust_String s = lust_string_new();
    lust_string_push_cstr(&s, what);
    lust_string_push_cstr(&s, ": need ");
    lust_fmt_u64(&s, need);
    lust_string_push_cstr(&s, " bytes to encode U+");
    lust_string_push_cstr(&s, hex);
    lust_string_push_cstr(&s, " but buffer has just ");
    lust_fmt_u64(&s, have);
    lust_panic_dyn(&s, loc);
})

/* `char::encode_utf8` into a caller buffer: the byte count written,
   or core's panic when the buffer is short. */
uint64_t lust_char_encode_utf8(uint32_t c, uint8_t *dst, uint64_t dst_len, lust_loc loc) LUST_BODY({
    uint64_t n = c < 0x80 ? 1 : c < 0x800 ? 2 : c < 0x10000 ? 3 : 4;
    if (dst_len < n) { lust_encode_panic("encode_utf8", n, c, dst_len, loc); return 0; }
    if (n == 1) {
        dst[0] = (uint8_t)c;
    } else if (n == 2) {
        dst[0] = (uint8_t)(0xC0 | (c >> 6));
        dst[1] = (uint8_t)(0x80 | (c & 0x3F));
    } else if (n == 3) {
        dst[0] = (uint8_t)(0xE0 | (c >> 12));
        dst[1] = (uint8_t)(0x80 | ((c >> 6) & 0x3F));
        dst[2] = (uint8_t)(0x80 | (c & 0x3F));
    } else {
        dst[0] = (uint8_t)(0xF0 | (c >> 18));
        dst[1] = (uint8_t)(0x80 | ((c >> 12) & 0x3F));
        dst[2] = (uint8_t)(0x80 | ((c >> 6) & 0x3F));
        dst[3] = (uint8_t)(0x80 | (c & 0x3F));
    }
    return n;
})

/* `char::encode_utf16` into a caller buffer: the unit count written,
   or core's panic (which says "bytes") when the buffer is short. */
uint64_t lust_char_encode_utf16(uint32_t c, uint16_t *dst, uint64_t dst_len, lust_loc loc) LUST_BODY({
    uint64_t n = c < 0x10000 ? 1 : 2;
    if (dst_len < n) { lust_encode_panic("encode_utf16", n, c, dst_len, loc); return 0; }
    if (n == 1) {
        dst[0] = (uint16_t)c;
    } else {
        uint32_t v = c - 0x10000;
        dst[0] = (uint16_t)(0xD800 + (v >> 10));
        dst[1] = (uint16_t)(0xDC00 + (v & 0x3FF));
    }
    return n;
})

/* UTF-8 validation with Rust's error report (core::str::validations::
   run_utf8_validation): 1 when `v` is valid; else 0 with the length of
   the valid prefix and the invalid sequence's length (1 to 3), or 0 when
   the input ends inside a sequence (Rust's `error_len() == None`). */
int lust_utf8_check(const uint8_t *v, uint64_t len, uint64_t *valid_up_to, uint8_t *error_len) LUST_BODY({
    uint64_t i = 0;
    while (i < len) {
        uint64_t start = i;
        uint8_t first = v[i];
        if (first < 0x80) {
            i++;
            /* An ASCII run: 16 bytes per step while none has its high bit, as core's
               validator skips ASCII by words (source text is mostly ASCII). */
            while (i + 16 <= len) {
                uint64_t a, b;
                memcpy(&a, v + i, 8);
                memcpy(&b, v + i + 8, 8);
                if ((a | b) & 0x8080808080808080ull) break;
                i += 16;
            }
            continue;
        }
        uint8_t el = 1;
        int w = (first >= 0xC2 && first <= 0xDF) ? 2 : (first >= 0xE0 && first <= 0xEF) ? 3 : (first >= 0xF0 && first <= 0xF4) ? 4 : 0;
        if (w == 0) goto bad;
        if (++i >= len) { el = 0; goto bad; }
        uint8_t b = v[i];
        if (w == 2) {
            if ((b & 0xC0) != 0x80) goto bad;
        } else {
            int ok = w == 3
                ? ((first == 0xE0 && b >= 0xA0 && b <= 0xBF) || (first >= 0xE1 && first <= 0xEC && b >= 0x80 && b <= 0xBF)
                   || (first == 0xED && b >= 0x80 && b <= 0x9F) || (first >= 0xEE && b >= 0x80 && b <= 0xBF))
                : ((first == 0xF0 && b >= 0x90 && b <= 0xBF) || (first >= 0xF1 && first <= 0xF3 && b >= 0x80 && b <= 0xBF)
                   || (first == 0xF4 && b >= 0x80 && b <= 0x8F));
            if (!ok) goto bad;
            el = 2;
            if (++i >= len) { el = 0; goto bad; }
            if ((v[i] & 0xC0) != 0x80) goto bad;
            if (w == 4) {
                el = 3;
                if (++i >= len) { el = 0; goto bad; }
                if ((v[i] & 0xC0) != 0x80) goto bad;
            }
        }
        i++;
        continue;
    bad:
        *valid_up_to = start;
        *error_len = el;
        return 0;
    }
    return 1;
})

/* `env::Args` (IterKind::Args): process argument `i` as a String. One
   that is not UTF-8 panics as std's `Args::next` (`back` 0) or
   `next_back` (`back` 1) does: `into_string().unwrap()` on an Err that
   prints the bytes with OsStr's Debug (valid runs as str Debug escapes
   them, each invalid byte as \xNN). */
lust_String lust_env_arg(uint64_t i, int back) LUST_BODY({
    lust_str a;
    a.ptr = (const uint8_t *)lust_argv[i];
    a.len = strlen(lust_argv[i]);
    uint64_t up;
    uint8_t el;
    if (lust_utf8_check(a.ptr, a.len, &up, &el)) return lust_string_from(a);
    lust_String s = lust_string_new();
    lust_string_push_cstr(&s, "called `Result::unwrap()` on an `Err` value: \"");
    uint64_t at = 0;
    while (at < a.len) {
        if (!lust_utf8_check(a.ptr + at, a.len - at, &up, &el)) {
            if (el == 0) el = (uint8_t)(a.len - at - up);
        } else {
            up = a.len - at;
            el = 0;
        }
        uint64_t j = at;
        while (j < at + up) lust_fmt_escape(&s, lust_utf8_next(a.ptr, &j), '"');
        for (uint64_t k = 0; k < el; k++) {
            char b[8];
            snprintf(b, sizeof b, "\\x%02X", a.ptr[at + up + k]);
            lust_string_push_cstr(&s, b);
        }
        at += up + el;
    }
    lust_string_push_cstr(&s, "\"");
    lust_panic(&s, back ? lust_std_loc(16, 914, 56) : lust_std_loc(16, 878, 51));
    return lust_string_new();
})

/* `Display` of `str::Utf8Error` (and `FromUtf8Error`, which shows its
   `Utf8Error`): Rust writes it with `write!`, so no padding applies. */
void lust_fmt_utf8_error(lust_String *out, uint64_t valid_up_to, uint32_t has_len, uint64_t len) LUST_BODY({
    if (has_len) {
        lust_string_push_cstr(out, "invalid utf-8 sequence of ");
        lust_fmt_u64(out, len);
        lust_string_push_cstr(out, " bytes from index ");
    } else {
        lust_string_push_cstr(out, "incomplete utf-8 byte sequence from index ");
    }
    lust_fmt_u64(out, valid_up_to);
})

/* char::to_digit. Returns 0xFFFFFFFF for "not a digit". */
uint32_t lust_digit(uint32_t c, uint32_t radix, lust_loc loc) LUST_BODY({
    if (radix < 2 || radix > 36) lust_panic_cstr("to_digit: invalid radix -- radix must be in the range 2 to 36 inclusive", loc);
    uint32_t d = c >= '0' && c <= '9' ? c - '0' : (c | 32) >= 'a' && (c | 32) <= 'z' ? (c | 32) - 'a' + 10 : 0xFFFFFFFFu;
    return d < radix ? d : 0xFFFFFFFFu;
})

/* char::from_digit. Returns 0xFFFFFFFF for "not a digit in this radix".
   A radix under 2 is not a panic in Rust: every check is digit < radix. */
uint32_t lust_from_digit(uint32_t digit, uint32_t radix, lust_loc loc) LUST_BODY({
    if (radix > 36) lust_panic_cstr("from_digit: radix is too high (maximum 36)", loc);
    if (digit >= radix) return 0xFFFFFFFFu;
    return digit < 10 ? '0' + digit : 'a' + digit - 10;
})

/* Float formatting, parsing, and casts (src/runtime/float.h). */
#include "float.h"

/* core::fmt: the Formatter, leaf impls, and Debug builders
   (src/runtime/fmt.h, W-STD-B). */
#include "fmt.h"

/* Slice sorting: Rust 1.99 driftsort and ipnsort (src/runtime/sort.h). */
#include "sort.h"

/* Erased hash table core (src/runtime/hash.h): declarations in every
   unit, bodies only in the runtime unit (LUST_IMPL). */
#include "hash.h"

/* Adapter crate cores, such as xxh3 (src/runtime/deps.h, W-DEPS). */
#include "deps.h"

#include "sync.c"

/* The std platform crate's syscalls (src/runtime/sys.h, W-SHIM). */
#include "sys.h"
/* The std platform crate's fd and process calls (src/runtime/sysio.h,
   W-SHIM phase 2). */
#include "sysio.h"
/* The socket calls behind std::net (src/runtime/sysnet.h,
   w-cinterop). */
#include "sysnet.h"
/* The Unix calls behind the rustix adapter (src/runtime/sysx.h,
   w-cinterop2). */
#include "sysx.h"
/* Std runtime hooks for time and fmt (src/runtime/stdc.h, W-STD-C). */
#include "stdc.h"
