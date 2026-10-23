/* Inline fast paths of the hottest small runtime helpers, for units an optimizing C
   compiler builds (release builds have no LTO, so each helper would be a call into the
   runtime unit: atomic loads, Once checks, leading_zeros, slice ranges and division were
   about 10% of a release tsgo's cycles). Each macro keeps its function's name, arguments
   and result; a slow path (a panic, a grow, a wait) calls that function, which a
   function-like macro does not expand inside its own body. cgen appends this text after
   the runtime declarations (`unit_header`); tcc units and the runtime unit itself call
   the functions, and so does a build with -DLUST_NO_INL (for A/B timing). */
#if !defined(__TINYC__) && !defined(LUST_IMPL) && !defined(LUST_NO_INL)
/* lust's atomic ordering (0 Relaxed, 1 Release, 2 Acquire, 3 AcqRel, 4 SeqCst) as a C
   memory order, as sync.c LUST_MO. A load's Release and AcqRel orders panic: the
   function does that. */
#define lust_inl_mo_(o) ((o) == 0 ? __ATOMIC_RELAXED : (o) == 1 ? __ATOMIC_RELEASE : (o) == 2 ? __ATOMIC_ACQUIRE : (o) == 3 ? __ATOMIC_ACQ_REL : __ATOMIC_SEQ_CST)
#define lust_inl_load_(N, U, p, o, loc)                                                                     \
    __extension__({                                                                                         \
        U *lust_p_ = (p);                                                                                   \
        uint32_t lust_o_ = (o);                                                                             \
        __builtin_expect(lust_o_ == 1 || lust_o_ == 3, 0) ? lust_at_load_##N(lust_p_, lust_o_, (loc))      \
                                                          : __atomic_load_n(lust_p_, lust_inl_mo_(lust_o_)); \
    })
#define lust_at_load_1(p, o, loc) lust_inl_load_(1, uint8_t, p, o, loc)
#define lust_at_load_2(p, o, loc) lust_inl_load_(2, uint16_t, p, o, loc)
#define lust_at_load_4(p, o, loc) lust_inl_load_(4, uint32_t, p, o, loc)
#define lust_at_load_8(p, o, loc) lust_inl_load_(8, uint64_t, p, o, loc)

/* A Once is set when its state is 2 (sync.c): no compare-exchange, no wait. */
#define lust_once_is_done(st) (__atomic_load_n((st), __ATOMIC_ACQUIRE) == 2)
#define lust_once_begin(st)                                                                         \
    __extension__({                                                                                 \
        uint32_t *lust_st_ = (st);                                                                  \
        __builtin_expect(__atomic_load_n(lust_st_, __ATOMIC_ACQUIRE) == 2, 1) ? 0 : lust_once_begin(lust_st_); \
    })

#define lust_leading_zeros64(v, bits)                                                                  \
    __extension__({                                                                                    \
        uint64_t lust_v_ = (v);                                                                        \
        unsigned lust_b_ = (bits);                                                                     \
        lust_v_ ? (uint32_t)(__builtin_clzll(lust_v_) - (64 - lust_b_)) : (uint32_t)lust_b_;           \
    })

/* A slice range in bounds; the function panics in Rust's order otherwise. */
#define lust_slice_range(lo, hi, inclusive, len, loc)                                                  \
    __extension__({                                                                                    \
        uint64_t lust_lo_ = (lo), lust_hi_ = (hi), lust_len_ = (len);                                  \
        int lust_inc_ = (inclusive);                                                                   \
        uint64_t lust_end_ = lust_inc_ ? lust_hi_ + 1 : lust_hi_;                                      \
        __builtin_expect(lust_lo_ <= lust_len_ && (lust_inc_ ? lust_hi_ < lust_len_ : lust_hi_ <= lust_len_) && lust_lo_ <= lust_end_, 1) \
            ? lust_end_                                                                                \
            : lust_slice_range(lust_lo_, lust_hi_, lust_inc_, lust_len_, (loc));                       \
    })

#define lust_div_u64(a, b, loc) \
    __extension__({ uint64_t lust_a_ = (a), lust_d_ = (b); __builtin_expect(lust_d_ != 0, 1) ? lust_a_ / lust_d_ : lust_div_u64(lust_a_, lust_d_, (loc)); })
#define lust_rem_u64(a, b, loc) \
    __extension__({ uint64_t lust_a_ = (a), lust_d_ = (b); __builtin_expect(lust_d_ != 0, 1) ? lust_a_ % lust_d_ : lust_rem_u64(lust_a_, lust_d_, (loc)); })
#define lust_div_i64(a, b, loc)                                                                         \
    __extension__({                                                                                     \
        int64_t lust_a_ = (a), lust_d_ = (b);                                                           \
        __builtin_expect(lust_d_ != 0 && !(lust_a_ == INT64_MIN && lust_d_ == -1), 1) ? lust_a_ / lust_d_ : lust_div_i64(lust_a_, lust_d_, (loc)); \
    })
#define lust_rem_i64(a, b, loc)                                                                         \
    __extension__({                                                                                     \
        int64_t lust_a_ = (a), lust_d_ = (b);                                                           \
        __builtin_expect(lust_d_ != 0 && !(lust_a_ == INT64_MIN && lust_d_ == -1), 1) ? lust_a_ % lust_d_ : lust_rem_i64(lust_a_, lust_d_, (loc)); \
    })

/* The C compiler's own memcpy and memmove: a small constant copy (a from_le_bytes, a
   moved value) becomes loads and stores instead of two calls. A macro whose arguments
   may be compound literals (`&(T){a, b}`, `(lust_u128){lo, hi}`: the comma in the braces
   splits a macro argument list) takes `...`; one that names them binds them with a
   struct initializer. */
#define lust_memcpy(...) ((void)__builtin_memcpy(__VA_ARGS__))
#define lust_memmove(...) ((void)__builtin_memmove(__VA_ARGS__))

/* A push or reserve that fits the capacity; growth (and zero-sized elements) take the
   function. A reserve_exact on an empty Vec (most of them: the first buffer of a collect or
   an extend) is one malloc here, as the function would do it: the element size is the call
   site's constant, so the size check (lust_vec_fits) folds. Any other case (an alignment
   over 16, an overflow, a failed malloc) is one call of the function. */
#define lust_vec_reserve_exact(v, extra, elem, align)                                                  \
    __extension__({                                                                                    \
        lust_Vec *lust_rv_ = (v);                                                                      \
        uint64_t lust_rx_ = (extra), lust_re_ = (elem), lust_ra_ = (align);                            \
        void *lust_rp_;                                                                                \
        if (lust_re_ == 0 || lust_rv_->cap - lust_rv_->len < lust_rx_) {                               \
            if (lust_re_ != 0 && lust_rv_->cap == 0 && lust_ra_ <= 16 && lust_vec_fits(lust_rx_, lust_re_) \
                && (lust_rp_ = __builtin_malloc(lust_rx_ * lust_re_)) != 0) {                          \
                lust_rv_->ptr = lust_rp_;                                                              \
                lust_rv_->cap = lust_rx_;                                                              \
            } else {                                                                                   \
                lust_vec_reserve_exact(lust_rv_, lust_rx_, lust_re_, lust_ra_);                        \
            }                                                                                          \
        }                                                                                              \
        (void)0;                                                                                       \
    })
#define lust_vec_push_slot(v, elem, align)                                                             \
    __extension__({                                                                                    \
        lust_Vec *lust_v_ = (v);                                                                       \
        uint64_t lust_e_ = (elem);                                                                     \
        __builtin_expect(lust_e_ != 0 && lust_v_->len < lust_v_->cap, 1)                              \
            ? (void *)((char *)lust_v_->ptr + (lust_v_->len++) * lust_e_)                              \
            : lust_vec_push_slot(lust_v_, lust_e_, (align));                                           \
    })
#define lust_vec_reserve(v, extra, elem, align)                                                        \
    __extension__({                                                                                    \
        lust_Vec *lust_v_ = (v);                                                                       \
        uint64_t lust_x_ = (extra), lust_e_ = (elem);                                                  \
        if (!__builtin_expect(lust_e_ != 0 && lust_v_->cap - lust_v_->len >= lust_x_, 1))             \
            lust_vec_reserve(lust_v_, lust_x_, lust_e_, (align));                                      \
        (void)0;                                                                                       \
    })
/* Atomic stores, swaps, compare-exchanges and fetch ops: the orders that panic take
   the function, as the narrow loads above. */
#define lust_inl_mo_cas_(s, f) (((f) == 4) ? __ATOMIC_SEQ_CST : ((f) == 2 && ((s) == 0 || (s) == 1)) ? ((s) == 0 ? __ATOMIC_ACQUIRE : __ATOMIC_ACQ_REL) : lust_inl_mo_(s))
#define lust_inl_store_(N, U, p, v, o, loc)                                                             \
    __extension__({                                                                                     \
        U *lust_p_ = (p);                                                                               \
        U lust_v_ = (v);                                                                                \
        uint32_t lust_o_ = (o);                                                                         \
        if (__builtin_expect(lust_o_ == 2 || lust_o_ == 3, 0)) lust_at_store_##N(lust_p_, lust_v_, lust_o_, (loc)); \
        else __atomic_store_n(lust_p_, lust_v_, lust_inl_mo_(lust_o_));                                 \
        (void)0;                                                                                        \
    })
#define lust_at_store_1(p, v, o, loc) lust_inl_store_(1, uint8_t, p, v, o, loc)
#define lust_at_store_2(p, v, o, loc) lust_inl_store_(2, uint16_t, p, v, o, loc)
#define lust_at_store_4(p, v, o, loc) lust_inl_store_(4, uint32_t, p, v, o, loc)
#define lust_at_store_8(p, v, o, loc) lust_inl_store_(8, uint64_t, p, v, o, loc)
#define lust_inl_cas_(N, U, p, cur, nv, s, f, old, weak)                                                \
    __extension__({                                                                                     \
        U *lust_p_ = (p);                                                                               \
        U lust_c_ = (cur), lust_n_ = (nv);                                                              \
        uint32_t lust_s_ = (s), lust_f_ = (f);                                                          \
        U *lust_old_ = (old);                                                                           \
        int lust_w_ = (weak), lust_ok_;                                                                 \
        if (__builtin_expect(lust_f_ == 1 || lust_f_ == 3, 0)) {                                        \
            lust_ok_ = lust_at_cas_##N(lust_p_, lust_c_, lust_n_, lust_s_, lust_f_, lust_old_, lust_w_); \
        } else {                                                                                        \
            U lust_e_ = lust_c_;                                                                        \
            lust_ok_ = __atomic_compare_exchange_n(lust_p_, &lust_e_, lust_n_, 0, lust_inl_mo_cas_(lust_s_, lust_f_), lust_inl_mo_(lust_f_)); \
            *lust_old_ = lust_e_;                                                                       \
        }                                                                                               \
        lust_ok_;                                                                                       \
    })
#define lust_at_cas_1(p, c, n, s, f, o, w) lust_inl_cas_(1, uint8_t, p, c, n, s, f, o, w)
#define lust_at_cas_2(p, c, n, s, f, o, w) lust_inl_cas_(2, uint16_t, p, c, n, s, f, o, w)
#define lust_at_cas_4(p, c, n, s, f, o, w) lust_inl_cas_(4, uint32_t, p, c, n, s, f, o, w)
#define lust_at_cas_8(p, c, n, s, f, o, w) lust_inl_cas_(8, uint64_t, p, c, n, s, f, o, w)
#define lust_at_swap_1(p, v, o) __atomic_exchange_n((p), (v), lust_inl_mo_(o))
#define lust_at_swap_2(p, v, o) __atomic_exchange_n((p), (v), lust_inl_mo_(o))
#define lust_at_swap_4(p, v, o) __atomic_exchange_n((p), (v), lust_inl_mo_(o))
#define lust_at_swap_8(p, v, o) __atomic_exchange_n((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_add_1(p, v, o) __atomic_fetch_add((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_add_2(p, v, o) __atomic_fetch_add((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_add_4(p, v, o) __atomic_fetch_add((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_add_8(p, v, o) __atomic_fetch_add((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_sub_1(p, v, o) __atomic_fetch_sub((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_sub_2(p, v, o) __atomic_fetch_sub((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_sub_4(p, v, o) __atomic_fetch_sub((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_sub_8(p, v, o) __atomic_fetch_sub((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_and_1(p, v, o) __atomic_fetch_and((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_and_2(p, v, o) __atomic_fetch_and((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_and_4(p, v, o) __atomic_fetch_and((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_and_8(p, v, o) __atomic_fetch_and((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_or_1(p, v, o) __atomic_fetch_or((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_or_2(p, v, o) __atomic_fetch_or((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_or_4(p, v, o) __atomic_fetch_or((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_or_8(p, v, o) __atomic_fetch_or((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_xor_1(p, v, o) __atomic_fetch_xor((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_xor_2(p, v, o) __atomic_fetch_xor((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_xor_4(p, v, o) __atomic_fetch_xor((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_xor_8(p, v, o) __atomic_fetch_xor((p), (v), lust_inl_mo_(o))

/* Bit counts with the compiler's builtins (the runtime loops for tcc; same results). */
#define lust_count_ones64(v) ((uint32_t)__builtin_popcountll((uint64_t)(v)))
#define lust_trailing_zeros64(v, bits)                                                                 \
    __extension__({                                                                                    \
        uint64_t lust_v_ = (v);                                                                        \
        uint32_t lust_b_ = (bits), lust_n_ = lust_v_ ? (uint32_t)__builtin_ctzll(lust_v_) : lust_b_;   \
        lust_n_ < lust_b_ ? lust_n_ : lust_b_;                                                         \
    })

/* Narrow division and remainder: zero (and MIN / -1) take the function, which panics. */
#define lust_inl_divu_(T, N, op, a, b, loc) \
    __extension__({ T lust_a_ = (a), lust_d_ = (b); __builtin_expect(lust_d_ != 0, 1) ? (T)(lust_a_ op lust_d_) : N(lust_a_, lust_d_, (loc)); })
#define lust_inl_divs_(T, MINV, N, op, a, b, loc)                                                       \
    __extension__({                                                                                     \
        T lust_a_ = (a), lust_d_ = (b);                                                                 \
        __builtin_expect(lust_d_ != 0 && !(lust_a_ == (MINV) && lust_d_ == -1), 1) ? (T)(lust_a_ op lust_d_) : N(lust_a_, lust_d_, (loc)); \
    })
#define lust_div_u8(a, b, loc) lust_inl_divu_(uint8_t, lust_div_u8, /, a, b, loc)
#define lust_rem_u8(a, b, loc) lust_inl_divu_(uint8_t, lust_rem_u8, %, a, b, loc)
#define lust_div_u16(a, b, loc) lust_inl_divu_(uint16_t, lust_div_u16, /, a, b, loc)
#define lust_rem_u16(a, b, loc) lust_inl_divu_(uint16_t, lust_rem_u16, %, a, b, loc)
#define lust_div_u32(a, b, loc) lust_inl_divu_(uint32_t, lust_div_u32, /, a, b, loc)
#define lust_rem_u32(a, b, loc) lust_inl_divu_(uint32_t, lust_rem_u32, %, a, b, loc)
#define lust_div_i8(a, b, loc) lust_inl_divs_(int8_t, -128, lust_div_i8, /, a, b, loc)
#define lust_rem_i8(a, b, loc) lust_inl_divs_(int8_t, -128, lust_rem_i8, %, a, b, loc)
#define lust_div_i16(a, b, loc) lust_inl_divs_(int16_t, -32768, lust_div_i16, /, a, b, loc)
#define lust_rem_i16(a, b, loc) lust_inl_divs_(int16_t, -32768, lust_rem_i16, %, a, b, loc)
#define lust_div_i32(a, b, loc) lust_inl_divs_(int32_t, -2147483647 - 1, lust_div_i32, /, a, b, loc)
#define lust_rem_i32(a, b, loc) lust_inl_divs_(int32_t, -2147483647 - 1, lust_rem_i32, %, a, b, loc)

/* An uncontended Mutex lock or unlock: one compare-exchange; a contended one (a waiter to
   wake, a wait) takes the function. */
#define lust_mutex_lock(st)                                                                             \
    __extension__({                                                                                     \
        uint32_t *lust_st_ = (st), lust_z_ = 0;                                                         \
        if (!__builtin_expect(__atomic_compare_exchange_n(lust_st_, &lust_z_, 1, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED), 1)) \
            lust_mutex_lock(lust_st_);                                                                  \
        (void)0;                                                                                        \
    })
#define lust_mutex_unlock(st)                                                                           \
    __extension__({                                                                                     \
        uint32_t *lust_st_ = (st), lust_one_ = 1;                                                       \
        if (!__builtin_expect(__atomic_compare_exchange_n(lust_st_, &lust_one_, 0, 0, __ATOMIC_RELEASE, __ATOMIC_RELAXED), 1)) \
            lust_mutex_unlock(lust_st_);                                                                \
        (void)0;                                                                                        \
    })

/* An empty Vec with no allocation (its dangling pointer is the alignment). */
#define lust_vec_with_capacity(n, elem, align)                                                         \
    __extension__({                                                                                    \
        uint64_t lust_n_ = (n), lust_e_ = (elem), lust_al_ = (align);                                  \
        __builtin_expect(lust_n_ == 0 && lust_e_ != 0, 1)                                              \
            ? (lust_Vec){(void *)(uintptr_t)(lust_al_ ? lust_al_ : 1), 0, 0}                           \
            : lust_vec_with_capacity(lust_n_, lust_e_, lust_al_);                                      \
    })

/* A str slice range in bounds with both ends on char boundaries; the function panics in
   Rust's order otherwise. */
#define lust_str_range(ptr, lo, hi, inclusive, len, loc)                                               \
    __extension__({                                                                                    \
        const uint8_t *lust_sp_ = (ptr);                                                               \
        uint64_t lust_lo_ = (lo), lust_hi_ = (hi), lust_len_ = (len);                                  \
        int lust_inc_ = (inclusive);                                                                   \
        uint64_t lust_end_ = lust_inc_ && lust_hi_ < lust_len_ ? lust_hi_ + 1 : lust_hi_;              \
        __builtin_expect(lust_lo_ <= lust_end_ && lust_end_ <= lust_len_ && !(lust_inc_ && lust_hi_ == lust_len_) \
                             && (lust_lo_ == lust_len_ || (lust_sp_[lust_lo_] & 0xC0) != 0x80)        \
                             && (lust_end_ == lust_len_ || (lust_sp_[lust_end_] & 0xC0) != 0x80), 1)  \
            ? lust_end_                                                                                \
            : lust_str_range(lust_sp_, lust_lo_, lust_hi_, lust_inc_, lust_len_, (loc));               \
    })

#define lust_string_as_str(s) __extension__({ lust_String *lust_s_ = (s); (lust_str){lust_s_->ptr, lust_s_->len}; })
#define lust_str_eq(...)                                                                               \
    __extension__({                                                                                    \
        struct { lust_str a, b; } lust_x_ = {__VA_ARGS__};                                             \
        (uint8_t)(lust_x_.a.len == lust_x_.b.len                                                       \
                  && (lust_x_.a.len == 0 || __builtin_memcmp(lust_x_.a.ptr, lust_x_.b.ptr, lust_x_.a.len) == 0)); \
    })

/* A thread-local's cell once the thread made it: thread.c's lust_tls_fast holds the cell
   pointers of the slots below LUST_TLS_FAST (one indexed thread-local load); a slot past it,
   or a cell this thread has not made yet, takes the function. */
extern __thread void *lust_tls_fast[];
#define lust_tls_cell(key, size, align)                                                                \
    __extension__({                                                                                    \
        uint64_t *lust_k_ = (key), lust_s_ = *lust_k_;                                                 \
        void *lust_c_ = __builtin_expect(lust_s_ < LUST_TLS_FAST, 1) ? lust_tls_fast[lust_s_] : (void *)0; \
        __builtin_expect(lust_c_ != 0, 1) ? lust_c_ : lust_tls_cell(lust_k_, (size), (align));         \
    })

/* Checked add, sub and mul of 64-bit and narrower integers (op 0, 1, 2) with the
   compiler's overflow builtins; division and 128 bits take the function. As the
   function: the wrapped result, masked to `bits`, goes to *out; 1 when it fits. */
#define lust_checked_op(a, b, bits, is_signed, op, out)                                                \
    __extension__({                                                                                    \
        uint64_t lust_a_ = (a), lust_b_ = (b), *lust_o_ = (out);                                       \
        unsigned lust_n_ = (bits);                                                                     \
        int lust_sg_ = (is_signed), lust_op_ = (op), lust_ok_;                                         \
        if (lust_n_ == 64 && lust_op_ <= 2 && lust_sg_) {                                              \
            int64_t lust_r_, lust_x_ = (int64_t)lust_a_, lust_y_ = (int64_t)lust_b_;                   \
            lust_ok_ = !(lust_op_ == 0   ? __builtin_add_overflow(lust_x_, lust_y_, &lust_r_)           \
                         : lust_op_ == 1 ? __builtin_sub_overflow(lust_x_, lust_y_, &lust_r_)           \
                                         : __builtin_mul_overflow(lust_x_, lust_y_, &lust_r_));         \
            *lust_o_ = (uint64_t)lust_r_;                                                              \
        } else if (lust_n_ == 64 && lust_op_ <= 2) {                                                   \
            uint64_t lust_r_;                                                                          \
            lust_ok_ = !(lust_op_ == 0   ? __builtin_add_overflow(lust_a_, lust_b_, &lust_r_)           \
                         : lust_op_ == 1 ? __builtin_sub_overflow(lust_a_, lust_b_, &lust_r_)           \
                                         : __builtin_mul_overflow(lust_a_, lust_b_, &lust_r_));         \
            *lust_o_ = lust_r_;                                                                        \
        } else if (lust_n_ <= 32 && lust_op_ <= 2) {                                                   \
            /* Exact in 64 bits: the result fits when it is in the type's range. */                   \
            uint64_t lust_m_ = (1ull << lust_n_) - 1ull;                                               \
            lust_a_ &= lust_m_;                                                                        \
            lust_b_ &= lust_m_;                                                                        \
            if (lust_sg_) {                                                                            \
                uint64_t lust_h_ = 1ull << (lust_n_ - 1);                                              \
                int64_t lust_x_ = (int64_t)((lust_a_ ^ lust_h_) - lust_h_), lust_y_ = (int64_t)((lust_b_ ^ lust_h_) - lust_h_); \
                int64_t lust_r_ = lust_op_ == 0 ? lust_x_ + lust_y_ : lust_op_ == 1 ? lust_x_ - lust_y_ : lust_x_ * lust_y_; \
                *lust_o_ = (uint64_t)lust_r_ & lust_m_;                                                \
                lust_ok_ = lust_r_ >= -(int64_t)lust_h_ && lust_r_ < (int64_t)lust_h_;                 \
            } else {                                                                                   \
                uint64_t lust_r_ = lust_op_ == 0 ? lust_a_ + lust_b_ : lust_op_ == 1 ? lust_a_ - lust_b_ : lust_a_ * lust_b_; \
                *lust_o_ = lust_r_ & lust_m_;                                                          \
                lust_ok_ = lust_op_ == 1 ? lust_a_ >= lust_b_ : lust_r_ <= lust_m_;                    \
            }                                                                                          \
        } else                                                                                         \
            lust_ok_ = lust_checked_op(lust_a_, lust_b_, lust_n_, lust_sg_, lust_op_, lust_o_);         \
        lust_ok_;                                                                                      \
    })

#ifdef __SIZEOF_INT128__
/* 128-bit compares, products and shifts with the compiler's __int128 (the functions
   build them from 64-bit halves). A shift of 128 or more takes the function. */
#define lust_inl_w_(x) (((unsigned __int128)(x).hi << 64) | (x).lo)
#define lust_inl_u128_of_(v)                                                                           \
    __extension__({                                                                                    \
        unsigned __int128 lust_w_ = (v);                                                               \
        (lust_u128){(uint64_t)lust_w_, (uint64_t)(lust_w_ >> 64)};                                     \
    })
#define lust_u128_cmp(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_u128 a, b; } lust_x_ = {__VA_ARGS__};                                            \
        unsigned __int128 lust_l_ = lust_inl_w_(lust_x_.a), lust_r_ = lust_inl_w_(lust_x_.b);          \
        (int32_t)((lust_l_ > lust_r_) - (lust_l_ < lust_r_));                                          \
    })
#define lust_i128_cmp(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_i128 a, b; } lust_x_ = {__VA_ARGS__};                                            \
        __int128 lust_l_ = (__int128)lust_inl_w_(lust_x_.a), lust_r_ = (__int128)lust_inl_w_(lust_x_.b); \
        (int32_t)((lust_l_ > lust_r_) - (lust_l_ < lust_r_));                                          \
    })
#define lust_u128_mul(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_u128 a, b; } lust_x_ = {__VA_ARGS__};                                            \
        lust_inl_u128_of_(lust_inl_w_(lust_x_.a) * lust_inl_w_(lust_x_.b));                            \
    })
#define lust_i128_mul(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_i128 a, b; } lust_x_ = {__VA_ARGS__};                                            \
        lust_u128 lust_p_ = lust_inl_u128_of_(lust_inl_w_(lust_x_.a) * lust_inl_w_(lust_x_.b));        \
        (lust_i128){lust_p_.lo, lust_p_.hi};                                                           \
    })
#define lust_u128_shl(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_u128 a; uint32_t n; } lust_x_ = {__VA_ARGS__};                                   \
        __builtin_expect(lust_x_.n < 128, 1) ? lust_inl_u128_of_(lust_inl_w_(lust_x_.a) << lust_x_.n)  \
                                             : lust_u128_shl(lust_x_.a, lust_x_.n);                    \
    })
#define lust_u128_shr(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_u128 a; uint32_t n; } lust_x_ = {__VA_ARGS__};                                   \
        __builtin_expect(lust_x_.n < 128, 1) ? lust_inl_u128_of_(lust_inl_w_(lust_x_.a) >> lust_x_.n)  \
                                             : lust_u128_shr(lust_x_.a, lust_x_.n);                    \
    })
/* Wrapping 128-bit add and sub, and the bitwise ops. */
#define lust_inl_u128_op_(T, op, ...)                                                                  \
    __extension__({                                                                                    \
        struct { T a, b; } lust_x_ = {__VA_ARGS__};                                                    \
        lust_u128 lust_r_ = lust_inl_u128_of_(lust_inl_w_(lust_x_.a) op lust_inl_w_(lust_x_.b));       \
        (T){lust_r_.lo, lust_r_.hi};                                                                   \
    })
#define lust_u128_add(...) lust_inl_u128_op_(lust_u128, +, __VA_ARGS__)
#define lust_u128_sub(...) lust_inl_u128_op_(lust_u128, -, __VA_ARGS__)
#define lust_i128_add(...) lust_inl_u128_op_(lust_i128, +, __VA_ARGS__)
#define lust_i128_sub(...) lust_inl_u128_op_(lust_i128, -, __VA_ARGS__)
#define lust_u128_and(...) lust_inl_u128_op_(lust_u128, &, __VA_ARGS__)
#define lust_u128_or(...) lust_inl_u128_op_(lust_u128, |, __VA_ARGS__)
#define lust_u128_xor(...) lust_inl_u128_op_(lust_u128, ^, __VA_ARGS__)
#endif

/* Small helpers that every unit called out of line: on tsgo's pgo-train they ran 200 M
   calls of 2 to 40 instructions each. Each keeps its function's arguments and result;
   a panic or a slow case calls the function. */

/* A hash table's item count and capacity (hash.c). */
#define lust_hash_len(t) __extension__({ const lust_hash_table *lust_t_ = (t); lust_t_->items; })
#define lust_hash_capacity(t) __extension__({ const lust_hash_table *lust_t_ = (t); lust_t_->items + lust_t_->growth_left; })
#define lust_hash_is_empty(t) __extension__({ const lust_hash_table *lust_t_ = (t); (int)(lust_t_->items == 0); })
/* The empty table with no allocation, as the function makes it. */
#define lust_hash_init(t, size, align)                                                                 \
    __extension__({                                                                                    \
        lust_hash_table *lust_t_ = (t);                                                                \
        uint64_t lust_al_ = (align);                                                                   \
        lust_t_->elem_size = (size);                                                                   \
        lust_t_->elem_align = lust_al_ ? lust_al_ : 1;                                                 \
        lust_t_->ctrl = (uint8_t *)lust_hash_static_empty;                                             \
        lust_t_->data = 0;                                                                             \
        lust_t_->alloc_base = 0;                                                                       \
        lust_t_->bucket_mask = 0;                                                                      \
        lust_t_->items = 0;                                                                            \
        lust_t_->growth_left = 0;                                                                      \
        (void)0;                                                                                       \
    })
/* A table with no allocation is the empty one: nothing to drop or free. */
#define lust_hash_drop_table(t, drop, ctx)                                                             \
    __extension__({                                                                                    \
        lust_hash_table *lust_t_ = (t);                                                                \
        if (!(lust_t_->alloc_base == 0 && lust_t_->items == 0)) lust_hash_drop_table(lust_t_, (drop), (ctx)); \
        (void)0;                                                                                       \
    })

/* An index in bounds is the result; the function panics with Rust's message otherwise. */
#define lust_bounds(i, len, loc)                                                                       \
    __extension__({                                                                                    \
        uint64_t lust_i_ = (i), lust_n_ = (len);                                                       \
        __builtin_expect(lust_i_ < lust_n_, 1) ? lust_i_ : lust_bounds(lust_i_, lust_n_, (loc));       \
    })
#define lust_vec_check_remove(v, i, loc)                                                               \
    __extension__({                                                                                    \
        lust_Vec *lust_v_ = (v);                                                                       \
        uint64_t lust_i_ = (i);                                                                        \
        if (__builtin_expect(lust_i_ >= lust_v_->len, 0)) lust_vec_check_remove(lust_v_, lust_i_, (loc)); \
        (void)0;                                                                                       \
    })

/* The char at *i of valid UTF-8, and *i moved past it: an ASCII byte here, a wider char
   in the function. */
#define lust_utf8_next(p, i)                                                                           \
    __extension__({                                                                                    \
        const uint8_t *lust_p_ = (p);                                                                  \
        uint64_t *lust_i_ = (i);                                                                       \
        uint8_t lust_b_ = lust_p_[*lust_i_];                                                           \
        __builtin_expect(lust_b_ < 0x80, 1) ? (*lust_i_ += 1, (uint32_t)lust_b_) : lust_utf8_next(lust_p_, lust_i_); \
    })
#define lust_chars(...) __extension__({ struct { lust_str s; } lust_x_ = {__VA_ARGS__}; (lust_Chars){lust_x_.s, 0}; })
#define lust_str_starts_with(...)                                                                      \
    __extension__({                                                                                    \
        struct { lust_str s, p; } lust_x_ = {__VA_ARGS__};                                             \
        (uint8_t)(lust_x_.p.len <= lust_x_.s.len                                                       \
                  && (lust_x_.p.len == 0 || __builtin_memcmp(lust_x_.s.ptr, lust_x_.p.ptr, lust_x_.p.len) == 0)); \
    })
#define lust_str_ends_with(...)                                                                        \
    __extension__({                                                                                    \
        struct { lust_str s, p; } lust_x_ = {__VA_ARGS__};                                             \
        (uint8_t)(lust_x_.p.len <= lust_x_.s.len                                                       \
                  && (lust_x_.p.len == 0                                                               \
                      || __builtin_memcmp(lust_x_.s.ptr + lust_x_.s.len - lust_x_.p.len, lust_x_.p.ptr, lust_x_.p.len) == 0)); \
    })

/* A range's start and end in a slice of `len` (`get(range)`), as core.c's function: the
   tags give each end's kind (end: 0 included, 1 excluded, 2 none; start: 0 included,
   1 excluded, 2 none); 0 when the range does not fit. */
static inline int lust_inl_range_bounds_get_(uint64_t len, uint64_t s_tag, uint64_t s_val, uint64_t e_tag, uint64_t e_val,
                                             uint64_t *out_s, uint64_t *out_e) {
    uint64_t end, start;
    if (e_tag == 0) {
        if (e_val >= len) return 0;
        end = e_val + 1;
    } else if (e_tag == 1) {
        if (e_val > len) return 0;
        end = e_val;
    } else {
        end = len;
    }
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
}
#define lust_range_bounds_get(...) lust_inl_range_bounds_get_(__VA_ARGS__)

/* Allocation: malloc for a nonzero size at an alignment malloc gives; zero sizes, larger
   alignments and a failed malloc (the function retries, then reports it) take the
   function. (__builtin_malloc calls malloc; units declare no malloc of their own, and a
   program's own extern malloc may declare it with other types.) free for a nonzero size,
   but Windows' over-aligned blocks. */
#define lust_alloc(size, align)                                                                        \
    __extension__({                                                                                    \
        uint64_t lust_sz_ = (size), lust_al_ = (align);                                                \
        void *lust_r_ = __builtin_expect(lust_sz_ != 0 && lust_al_ <= 16, 1) ? __builtin_malloc(lust_sz_) : 0; \
        __builtin_expect(lust_r_ != 0, 1) ? lust_r_ : lust_alloc(lust_sz_, lust_al_);                  \
    })
#ifdef _WIN32
#define lust_inl_aligned_free_(align) ((align) > 16)
#else
#define lust_inl_aligned_free_(align) 0
#endif
#define lust_dealloc(ptr, size, align)                                                                 \
    __extension__({                                                                                    \
        void *lust_p_ = (ptr);                                                                         \
        uint64_t lust_sz_ = (size), lust_al_ = (align);                                                \
        if (lust_sz_) {                                                                                \
            if (lust_inl_aligned_free_(lust_al_)) lust_dealloc(lust_p_, lust_sz_, lust_al_);           \
            else free(lust_p_);                                                                        \
        }                                                                                              \
        (void)0;                                                                                       \
    })

/* Strings: the empty one, drop, and a push that fits the capacity (growth takes the
   function). */
#define lust_string_new() ((lust_String){(uint8_t *)(uintptr_t)1, 0, 0})
#define lust_string_drop(s) __extension__({ lust_String *lust_s_ = (s); lust_dealloc(lust_s_->ptr, lust_s_->cap, 1); })
#define lust_string_push_str(s, ...)                                                                   \
    __extension__({                                                                                    \
        lust_String *lust_s_ = (s);                                                                    \
        struct { lust_str x; } lust_x_ = {__VA_ARGS__};                                                \
        if (__builtin_expect(lust_s_->cap - lust_s_->len >= lust_x_.x.len, 1)) {                       \
            if (lust_x_.x.len) __builtin_memcpy(lust_s_->ptr + lust_s_->len, lust_x_.x.ptr, lust_x_.x.len); \
            lust_s_->len += lust_x_.x.len;                                                             \
        } else                                                                                         \
            lust_string_push_str(lust_s_, lust_x_.x);                                                  \
        (void)0;                                                                                       \
    })
#define lust_string_push_char(s, c)                                                                    \
    __extension__({                                                                                    \
        lust_String *lust_s_ = (s);                                                                    \
        uint32_t lust_c_ = (c);                                                                        \
        if (__builtin_expect(lust_c_ < 0x80 && lust_s_->len < lust_s_->cap, 1))                        \
            lust_s_->ptr[lust_s_->len++] = (uint8_t)lust_c_;                                           \
        else                                                                                           \
            lust_string_push_char(lust_s_, lust_c_);                                                   \
        (void)0;                                                                                       \
    })

/* f64 and f32 min and max as float.c: a NaN loses to a number, and of two equal values
   (0.0 and -0.0) the second wins. The integer to float casts round to nearest, ties to
   even, as Rust's `as` (the runtime builds them from integer steps for tcc). */
/* Equal operands: as float.c's lust_f64_min (the target's tie rule). */
#if defined(__aarch64__)
static inline int lust_inl_fneg_(double x) { return x < 0 || (x == 0 && 1.0 / x < 0); }
#define LUST_INL_TIE_(a, b, want_neg) (lust_inl_fneg_(a) == (want_neg) ? (a) : (b))
#else
#define LUST_INL_TIE_(a, b, want_neg) (b)
#endif
static inline double lust_inl_f64_min_(double a, double b) { return a < b ? a : b < a ? b : a == b ? LUST_INL_TIE_(a, b, 1) : a == a ? a : b; }
static inline double lust_inl_f64_max_(double a, double b) { return a > b ? a : b > a ? b : a == b ? LUST_INL_TIE_(a, b, 0) : a == a ? a : b; }
static inline float lust_inl_f32_min_(float a, float b) { return a < b ? a : b < a ? b : a == b ? LUST_INL_TIE_(a, b, 1) : a == a ? a : b; }
static inline float lust_inl_f32_max_(float a, float b) { return a > b ? a : b > a ? b : a == b ? LUST_INL_TIE_(a, b, 0) : a == a ? a : b; }
#define lust_f64_min(a, b) lust_inl_f64_min_((a), (b))
#define lust_f64_max(a, b) lust_inl_f64_max_((a), (b))
#define lust_f32_min(a, b) lust_inl_f32_min_((a), (b))
#define lust_f32_max(a, b) lust_inl_f32_max_((a), (b))
#define lust_u64_to_f64(v) ((double)(uint64_t)(v))
#define lust_i64_to_f64(v) ((double)(int64_t)(v))
#endif

/* `p` is a reference made just before (Rust's validity invariant: never null). cgen states
   it only on the path that makes the reference, never on a pointer that may be null: a slice
   element `&ptr[i]` inside its bounds check, the payload of a `Some(r)` the program builds.
   A later niche check of the `Option<&T>` (`p != 0`) then folds. tcc ignores it. */
#if !defined(__TINYC__)
#define lust_ref_nn(p)                       \
    do {                                     \
        if (!(p)) __builtin_unreachable();   \
    } while (0)
#else
#define lust_ref_nn(p) ((void)0)
#endif

/* A release fn's constant data named by its content (cgen/kconst.rs `kdata_def`): each unit
   that uses it defines it, and the link keeps one definition, so equal constants share one
   address program-wide with no run-time interning. clang's selectany is a comdat (weak_odr):
   its value folds into the code that reads it, as a constant's does (a compare with a
   promoted enum constant is a compare with an immediate). A plain weak definition (gcc)
   keeps the identity but not the folding. */
#if defined(_WIN32)
#define LUST_KDATA __declspec(selectany)
#elif defined(__clang__)
#define LUST_KDATA __attribute__((selectany, visibility("hidden")))
#else
#define LUST_KDATA __attribute__((weak, visibility("hidden")))
#endif
