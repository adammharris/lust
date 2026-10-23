/* The std platform crate's fd and process runtime (W-SHIM phase 2):
   the C behind the `sys_fd_*`, `sys_stdin_*`, and `sys_proc_*`
   intrinsics of src/ty/lang.rs, called from library/std/src/io.rs,
   fs.rs, and process_os.rs. A `&[u8]` argument (SigTy::Bytes) arrives
   as a pointer and a length; `&mut Vec<u8>` arrives as a pointer to
   the runtime struct. OS errors return as errno values (positive),
   or as -errno where the value is a count.

   Declarations here are in every unit; bodies (sysio.c) only in the
   runtime unit (LUST_IMPL), like sys.h. */
#ifndef LUST_RT_SYSIO_H
#define LUST_RT_SYSIO_H

/* One read(2) of up to `max` bytes from `fd`, appended to the Vec:
   the count read, or -errno. Lust reads through a staging Vec because
   the read target is a caller byte buffer (`Read::read`). */
int64_t lust_sys_fd_read(int32_t fd, uint64_t max, lust_Vec *out);
/* One write(2) of the bytes to `fd`: the count written, or -errno. */
int64_t lust_sys_fd_write(int32_t fd, const uint8_t *p, uint64_t len);
/* close(2): 0, or errno. */
int32_t lust_sys_fd_close(int32_t fd);
/* dup(2) with FD_CLOEXEC: the new fd, or -errno. */
int32_t lust_sys_fd_dup(int32_t fd);
/* fsync(2): 0, or errno. */
int32_t lust_sys_fd_sync(int32_t fd);
/* fdatasync(2): 0, or errno. */
int32_t lust_sys_fd_sync_data(int32_t fd);
/* ftruncate(2) to `len`: 0, or errno. */
int32_t lust_sys_fd_truncate(int32_t fd, uint64_t len);
/* lseek(2) `off` from `whence` (0 start, 1 current, 2 end): the new
   position, or -errno. */
int64_t lust_sys_fd_seek(int32_t fd, int64_t off, int32_t whence);
/* pread of up to max bytes at off, appended to out: the count or -errno. */
int64_t lust_sys_fd_pread(int32_t fd, uint64_t max, int64_t off, lust_Vec *out);
/* pwrite of the bytes at off: the count or -errno. */
int64_t lust_sys_fd_pwrite(int32_t fd, const uint8_t *p, uint64_t len, int64_t off);
/* isatty: 1 or 0. */
int32_t lust_sys_fd_isatty(int32_t fd);
/* fstat(2) as 8-byte little-endian fields appended to the Vec (the
   same layout as lust_sys_stat): 0, or errno. */
int32_t lust_sys_fd_stat(int32_t fd, lust_Vec *out);
/* The path an open fd names, appended to the Vec: 0, or errno. */
int32_t lust_sys_fd_path(int32_t fd, lust_Vec *out);
/* open(2) of a path with std's flags for `flags` (see sysio.c) and
   mode 0666: the fd, -errno, or -1 for a path with a NUL byte as an
   errno of 0 is impossible, so -1 reads back as the NUL error only
   when the caller checked the path for NUL itself. Callers check. */
int32_t lust_sys_fd_open(const uint8_t *p, uint64_t len, int32_t flags);
/* lust_sys_fd_open plus std's custom flags (OR'd in) and creation mode,
   retried on EINTR as std's open_c: the fd or -errno. */
int32_t lust_sys_fd_open_ext(const uint8_t *p, uint64_t len, int32_t flags, int32_t custom, uint32_t mode);

/* Stdin (fd 0) through one process-wide buffer, as std's stdin: bytes
   a lock buffered stay available to later reads. read appends up to
   `max` bytes (from the buffer, else one read(2)): the count, or
   -errno. fill appends the buffered bytes without consuming them
   (one read(2) first when the buffer is empty): the count, or
   -errno. consume drops up to `n` buffered bytes. */
int64_t lust_sys_stdin_read(uint64_t max, lust_Vec *out);
int64_t lust_sys_stdin_fill(lust_Vec *out);
void lust_sys_stdin_consume(uint64_t n);

/* Spawning (std::process): posix_spawnp of `prog` with the packed
   argument, environment, and working-directory bytes the Rust side
   built (formats in sysio.c and process_os.rs). stdio spec per stream
   (stdin, stdout, stderr), packed into `stdio` as three bytes plus a
   byte that says the working directory is set: 0 inherit, 1 null,
   2 pipe, 3 the fd in that stream's slot of `fds` (three packed
   8-byte little-endian fds). On success, appends four 8-byte fields
   to `out`: the pid, then the parent ends of the stdin, stdout, and
   stderr pipes (-1 when not piped). Returns 0, errno, or -1 for a
   NUL byte in any string. */
int32_t lust_sys_proc_spawn(const uint8_t *prog, uint64_t proglen, const uint8_t *args, uint64_t argslen,
                            const uint8_t *env, uint64_t envlen, const uint8_t *cwd, uint64_t cwdlen, uint32_t stdio,
                            const uint8_t *fds, uint64_t fdslen, lust_Vec *out);
/* std's `CommandExt::exec` in this process (no fork): with the same
   packed inputs as lust_sys_proc_spawn, dup2 the configured stdio,
   chdir, SIGPIPE back to its default, then execvp with `environ`
   swapped for the packed environment when it changed (restored when
   the exec fails). Returns only on failure: the errno. */
int32_t lust_sys_proc_exec(const uint8_t *prog, uint64_t proglen, const uint8_t *args, uint64_t argslen,
                           const uint8_t *env, uint64_t envlen, const uint8_t *cwd, uint64_t cwdlen, uint32_t stdio,
                           const uint8_t *fds, uint64_t fdslen);
/* waitpid(2) on `pid` (blocking when `block`): the raw wait status,
   -2 when a non-blocking wait finds the child still running, or
   -errno. */
int64_t lust_sys_proc_wait(uint32_t pid, uint8_t block);
/* kill(2) with SIGKILL: 0, or errno. */
int32_t lust_sys_proc_kill(uint32_t pid);
/* Reads two fds to EOF with poll(2), appending to the two Vecs (a fd
   of -1 is skipped): 0, or errno of the first failed read. Used by
   `Command::output`, which must drain both pipes at once. */
int32_t lust_sys_fd_read_both(int32_t fd1, lust_Vec *out1, int32_t fd2, lust_Vec *out2);

#ifdef LUST_IMPL
#include "sysio.c"
#endif

#endif
