/* core::fmt for the lust runtime (W-STD-B): the Formatter, its sinks,
   pad and pad_integral, the leaf Display/Debug impls of the builtin
   types, and the Debug builders. A port of Rust 1.99
   core/src/fmt/{mod,builders,num}.rs, kept to the same write sequence
   where output can see it.

   Every fmt operation returns 0 for Ok(()) and 1 for Err(fmt::Error).
   Generated code calls these from format strings and from the Debug and
   Display glue (cgen::fmt), and user fmt impls reach them through
   `&mut Formatter` (a lust_Formatter pointer).

   Declarations here are in every unit; bodies (fmt.c) only in the
   runtime unit (LUST_IMPL), like float.h. */
#ifndef LUST_RT_FMT_H
#define LUST_RT_FMT_H

/* fmt::Alignment plus Rust's "unknown" (no alignment written). */
#define LUST_ALIGN_LEFT 0u
#define LUST_ALIGN_RIGHT 1u
#define LUST_ALIGN_CENTER 2u
#define LUST_ALIGN_UNKNOWN 3u

/* Formatter flags, one bit each: `+`, `-`, `#`, `0`, `x?`, `X?`, and
   whether a width or a precision was given. */
#define LUST_FLAG_PLUS 1u
#define LUST_FLAG_MINUS 2u
#define LUST_FLAG_ALT 4u
#define LUST_FLAG_ZERO 8u
#define LUST_FLAG_DEBUG_LOWER_HEX 16u
#define LUST_FLAG_DEBUG_UPPER_HEX 32u
#define LUST_FLAG_WIDTH 64u
#define LUST_FLAG_PREC 128u

/* One fmt::Write destination. `write` appends n bytes (valid UTF-8 in
   whole chars) and returns 0 or 1. `direct` is the String a plain
   String sink appends to, so leaf code may append there in one step;
   it is NULL for every other sink. `write_char` is the destination's
   own `write_char`, which core's Formatter calls for each fill, sign,
   and quote char (NULL: the char's UTF-8 text goes to `write`), and
   `keep_empty` makes `Formatter::write_str("")` reach `write`, as core
   calls `write_str` with it: both are a user writer's (cgen/fmt.rs
   `fmt_write_glue`), whose methods see every call. */
typedef struct lust_sink lust_sink;
struct lust_sink {
    int (*write)(lust_sink *self, const uint8_t *p, uint64_t n);
    lust_String *direct;
    int (*write_char)(lust_sink *self, uint32_t c);
    uint8_t keep_empty;
};

/* A sink over a user `impl fmt::Write` value `self` (its `write_fmt`
   default): `write` and `write_char` call the writer's methods. */
typedef struct {
    lust_sink base;
    void *self;
} lust_user_sink;
void lust_user_sink_init(lust_user_sink *k, void *self, int (*write)(lust_sink *, const uint8_t *, uint64_t), int (*write_char)(lust_sink *, uint32_t));
/* The UTF-8 bytes of char `c` into `b` (4 bytes): their count. */
int lust_utf8_char(uint32_t c, uint8_t *b);

/* builders::PadAdapter: indents each line written through it by four
   spaces. `on_newline` is the PadAdapterState it shares. */
typedef struct {
    lust_sink base;
    lust_sink *inner;
    uint8_t *on_newline;
} lust_pad_sink;

/* fmt::Formatter: the options of one placeholder and the sink. Width
   and precision are u16 in Rust 1.99; they are 0 when their flag is
   not set. */
typedef struct {
    lust_sink *buf;
    uint32_t fill;
    uint8_t align;
    uint8_t flags;
    uint16_t width;
    uint16_t prec;
} lust_Formatter;

/* Storage for one PadAdapter-wrapped Formatter (the `slot` and `state`
   of a builder call in pretty mode). */
typedef struct {
    lust_pad_sink pad;
    lust_Formatter f;
    uint8_t state;
} lust_fmt_slot;

/* The Debug builders (fmt::DebugStruct and kin). `err` is the stored
   fmt::Result. */
typedef struct {
    lust_Formatter *fmt;
    uint8_t err;
    uint8_t has_fields;
} lust_DebugStruct;
typedef struct {
    lust_Formatter *fmt;
    uint64_t fields;
    uint8_t err;
    uint8_t empty_name;
} lust_DebugTuple;
/* DebugList and DebugSet (builders::DebugInner); `set` picks the braces. */
typedef struct {
    lust_Formatter *fmt;
    uint8_t err;
    uint8_t has_fields;
    uint8_t set;
} lust_DebugList;
typedef struct {
    lust_Formatter *fmt;
    uint8_t err;
    uint8_t has_fields;
    uint8_t has_key;
    uint8_t state;
} lust_DebugMap;

/* fmt::Arguments (cgen format_args_value): `fmt` formats the parts of
   one format_args! site into a sink through a fresh Formatter, reading
   the argument references from `env`, and returns 0 (Ok) or 1 (Err).
   It is NULL for literal-only text (`text`, `len`). `cap` is the
   site's `estimated_capacity`, for `to_string`. */
typedef struct {
    int (*fmt)(const void *env, lust_sink *k);
    const void *env;
    const char *text;
    uint64_t len;
    uint64_t cap;
} lust_Arguments;

/* Sizes the compiler's layout tables assume (cgen fmt_size_align). */
_Static_assert(sizeof(lust_Formatter) == 24 && sizeof(lust_DebugTuple) == 24, "fmt layout");
_Static_assert(sizeof(lust_Arguments) == 40, "fmt layout");
_Static_assert(sizeof(lust_DebugStruct) == 16 && sizeof(lust_DebugList) == 16 && sizeof(lust_DebugMap) == 16, "fmt layout");

/* A sink over a String, and a Formatter with default options over a
   sink (Formatter::new: fill ' ', no alignment, no flags). */
void lust_sink_string(lust_sink *k, lust_String *s);
/* `print!` (to_stderr 0) and `eprint!` (1): locks the stream for the
   whole print, as std does (the lock is recursive, so a print inside a
   fmt impl goes on, and another thread's print waits), and makes `k` a
   sink that writes each piece to it. `lust_print_end` unlocks. */
void lust_print_begin(lust_sink *k, int to_stderr);
void lust_print_end(int to_stderr);
/* The sink of `io::Write::write_fmt` on a std stream: like the print
   sink, but a failed write records its errno in `err` and returns a
   fmt error instead of panicking, so the caller can build the
   `io::Error`. `lust_io_begin` locks the stream as `lust_print_begin`
   does; `lust_print_end` unlocks it. */
typedef struct {
    lust_sink base;
    int32_t err;
} lust_io_sink;
void lust_io_begin(lust_io_sink *k, int to_stderr);
void lust_f_init(lust_Formatter *f, lust_sink *buf);
/* fmt::Arguments: `fmt::write(k, a)`; Display and Debug of `a` into
   `f` (core writes to `f`'s sink and ignores `f`'s options); and
   `a.to_string()` (alloc's `fmt::format`). */
int lust_args_write(const lust_Arguments *a, lust_sink *k);
int lust_f_args(lust_Formatter *f, const lust_Arguments *a);
lust_String lust_args_to_string(const lust_Arguments *a);
/* Sets the options of one placeholder. `width` and `prec` count only
   when their flag bit is set. */
void lust_f_set(lust_Formatter *f, uint32_t fill, uint32_t align, uint32_t flags, uint32_t width, uint32_t prec);

int lust_f_write(lust_Formatter *f, const void *p, uint64_t n);
int lust_f_write_str(lust_Formatter *f, lust_str s);
int lust_f_write_char(lust_Formatter *f, uint32_t c);
/* Formatter::pad and Formatter::pad_integral. */
int lust_f_pad(lust_Formatter *f, lust_str s);
int lust_f_pad_integral(lust_Formatter *f, int nonneg, lust_str prefix, lust_str digits);

/* Integer Display (decimal), radix formats (mode 1 x, 2 X, 3 o, 4 b,
   over the value's bits at its type width), and Debug (Display unless
   the `x?` or `X?` flag asks for hex; `mask` cuts a signed value to its
   type width for that case). */
int lust_f_u64(lust_Formatter *f, uint64_t v);
int lust_f_i64(lust_Formatter *f, int64_t v);
int lust_f_u128(lust_Formatter *f, lust_u128 v);
int lust_f_i128(lust_Formatter *f, lust_i128 v);
int lust_f_radix(lust_Formatter *f, uint64_t lo, uint64_t hi, uint32_t mode);
int lust_f_dbg_u64(lust_Formatter *f, uint64_t v);
int lust_f_dbg_i64(lust_Formatter *f, int64_t v, uint64_t mask);
int lust_f_dbg_u128(lust_Formatter *f, lust_u128 v);
int lust_f_dbg_i128(lust_Formatter *f, lust_i128 v);
/* Floats in a LUST_FLOAT_* mode, with the Formatter's options. */
int lust_f_f64(lust_Formatter *f, double v, uint32_t mode);
int lust_f_f32(lust_Formatter *f, float v, uint32_t mode);
/* bool (Display and Debug), char Display, char and str Debug, `()`
   Debug, and fn pointer Debug (an address). */
int lust_f_bool(lust_Formatter *f, uint8_t v);
int lust_f_char(lust_Formatter *f, uint32_t c);
int lust_f_dbg_char(lust_Formatter *f, uint32_t c);
int lust_f_dbg_str(lust_Formatter *f, lust_str s);
int lust_f_unit(lust_Formatter *f);
int lust_f_fnptr(lust_Formatter *f, const void *p);
int lust_f_pointer(lust_Formatter *f, const void *p);
uint32_t lust_f_count(uint64_t n, lust_loc loc);

/* The builders. A `*_field`/`*_entry`/`*_key`/`*_value` call returns the
   Formatter the value writes to (the builder's own, or a PadAdapter in
   `slot` when the Formatter is alternate), or NULL when the stored
   result is already an error (then skip the value and the end call).
   The matching `*_end` call takes the value's result. */
void lust_dstruct_new(lust_DebugStruct *d, lust_Formatter *f, lust_str name);
lust_Formatter *lust_dstruct_field(lust_DebugStruct *d, lust_fmt_slot *s, lust_str name);
void lust_dstruct_field_end(lust_DebugStruct *d, lust_fmt_slot *s, int err);
int lust_dstruct_finish(lust_DebugStruct *d);
int lust_dstruct_finish_ne(lust_DebugStruct *d);
void lust_dtuple_new(lust_DebugTuple *d, lust_Formatter *f, lust_str name);
lust_Formatter *lust_dtuple_field(lust_DebugTuple *d, lust_fmt_slot *s);
void lust_dtuple_field_end(lust_DebugTuple *d, lust_fmt_slot *s, int err);
int lust_dtuple_finish(lust_DebugTuple *d);
int lust_dtuple_finish_ne(lust_DebugTuple *d);
void lust_dlist_new(lust_DebugList *d, lust_Formatter *f, int set);
lust_Formatter *lust_dlist_entry(lust_DebugList *d, lust_fmt_slot *s);
void lust_dlist_entry_end(lust_DebugList *d, lust_fmt_slot *s, int err);
int lust_dlist_finish(lust_DebugList *d);
int lust_dlist_finish_ne(lust_DebugList *d);
void lust_dmap_new(lust_DebugMap *d, lust_Formatter *f);
lust_Formatter *lust_dmap_key(lust_DebugMap *d, lust_fmt_slot *s, lust_loc loc);
void lust_dmap_key_end(lust_DebugMap *d, lust_fmt_slot *s, int err);
lust_Formatter *lust_dmap_value(lust_DebugMap *d, lust_fmt_slot *s, lust_loc loc);
void lust_dmap_value_end(lust_DebugMap *d, lust_fmt_slot *s, int err);
int lust_dmap_finish(lust_DebugMap *d, lust_loc loc);
int lust_dmap_finish_ne(lust_DebugMap *d, lust_loc loc);

/* The panic after a fmt impl returned Err into a sink that cannot fail:
   `what` 0 is format!, 1 is to_string, 2 is print! and eprint!
   (Rust's texts and std locations; a print has written the pieces
   before the failing one). */
void lust_fmt_failed(uint32_t what, lust_loc loc);

#ifdef LUST_IMPL
#include "fmt.c"
#endif

#endif
