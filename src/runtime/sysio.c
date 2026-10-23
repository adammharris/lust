#ifdef _WIN32
#include "sysiowin.c"
#else
/* Bodies of the fd and process intrinsics declared in sysio.h
   (W-SHIM phase 2). */
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

extern char **environ;

/* glibc exposes pipe2 only under a feature macro this unit does not
   set; declare it (the symbol is always in libc). Darwin has no
   pipe2: pipe plus the two flags this file passes, set right after
   (not atomic, as everywhere before pipe2 existed; a fork+exec in
   another thread in between could inherit the fds for a moment). */
#ifdef __APPLE__
static int lust_pipe2(int fds[2], int flags) {
    if (pipe(fds) != 0) return -1;
    for (int i = 0; i < 2; i++) {
        if (flags & O_CLOEXEC) fcntl(fds[i], F_SETFD, FD_CLOEXEC);
        if (flags & O_NONBLOCK) fcntl(fds[i], F_SETFL, O_NONBLOCK);
    }
    return 0;
}
#else
int pipe2(int pipefd[2], int flags);
static int lust_pipe2(int fds[2], int flags) { return pipe2(fds, flags); }
#endif

/* Appends `n` bytes to a Vec<u8>. */
static void lust_sysio_push(lust_Vec *out, const void *p, uint64_t n) {
    if (n == 0) return;
    lust_vec_reserve(out, n, 1, 1);
    memcpy((uint8_t *)out->ptr + out->len, p, (size_t)n);
    out->len += n;
}

/* One read into a fresh heap buffer, appended to the Vec. A zero
   max still makes the syscall (its error, or 0), as std and rustix do. */
int64_t lust_sys_fd_read(int32_t fd, uint64_t max, lust_Vec *out) {
    if (max == 0) {
        uint8_t none;
        ssize_t z = read(fd, &none, 0);
        return z < 0 ? -(int64_t)errno : (int64_t)z;
    }
    uint8_t *tmp = malloc((size_t)max);
    if (!tmp) lust_oom();
    ssize_t n = read(fd, tmp, (size_t)max);
    if (n < 0) {
        int e = errno;
        free(tmp);
        return -(int64_t)e;
    }
    lust_sysio_push(out, tmp, (uint64_t)n);
    free(tmp);
    return (int64_t)n;
}

int64_t lust_sys_fd_write(int32_t fd, const uint8_t *p, uint64_t len) {
    ssize_t n = write(fd, p, (size_t)len);
    if (n < 0) return -(int64_t)errno;
    return (int64_t)n;
}

int32_t lust_sys_fd_close(int32_t fd) { return close(fd) == 0 ? 0 : errno; }

int32_t lust_sys_fd_dup(int32_t fd) {
    int n = fcntl(fd, F_DUPFD_CLOEXEC, 0);
    return n < 0 ? -errno : n;
}

/* On Darwin std's sync_all and sync_data are both fcntl(F_FULLFSYNC)
   (std sys/fs/unix.rs os_fsync/os_datasync for target_vendor apple):
   a plain fsync there does not ask the drive to flush. */
#ifdef __APPLE__
#define LUST_F_FULLFSYNC 51
int32_t lust_sys_fd_sync(int32_t fd) { return fcntl(fd, LUST_F_FULLFSYNC) == 0 ? 0 : errno; }

int32_t lust_sys_fd_sync_data(int32_t fd) { return fcntl(fd, LUST_F_FULLFSYNC) == 0 ? 0 : errno; }
#else
int32_t lust_sys_fd_sync(int32_t fd) { return fsync(fd) == 0 ? 0 : errno; }

int32_t lust_sys_fd_sync_data(int32_t fd) { return fdatasync(fd) == 0 ? 0 : errno; }
#endif

int32_t lust_sys_fd_truncate(int32_t fd, uint64_t len) { return ftruncate(fd, (off_t)len) == 0 ? 0 : errno; }

int64_t lust_sys_fd_seek(int32_t fd, int64_t off, int32_t whence) {
    off_t r = lseek(fd, (off_t)off, whence == 0 ? SEEK_SET : whence == 1 ? SEEK_CUR : SEEK_END);
    return r < 0 ? -(int64_t)errno : (int64_t)r;
}

int64_t lust_sys_fd_pread(int32_t fd, uint64_t max, int64_t off, lust_Vec *out) {
    uint8_t none;
    uint8_t *tmp = max ? malloc((size_t)max) : &none;
    if (!tmp) lust_oom();
    ssize_t n = pread(fd, tmp, (size_t)max, (off_t)off);
    if (n < 0) {
        int e = errno;
        if (max) free(tmp);
        return -(int64_t)e;
    }
    lust_sysio_push(out, tmp, (uint64_t)n);
    if (max) free(tmp);
    return (int64_t)n;
}

int64_t lust_sys_fd_pwrite(int32_t fd, const uint8_t *p, uint64_t len, int64_t off) {
    ssize_t n = pwrite(fd, p, (size_t)len, (off_t)off);
    if (n < 0) return -(int64_t)errno;
    return (int64_t)n;
}

int32_t lust_sys_fd_isatty(int32_t fd) { return isatty(fd) ? 1 : 0; }

/* The path an open fd names, as std's File Debug finds it: fcntl(F_GETPATH)
   on Darwin, the /proc/self/fd link elsewhere. 0, or errno. */
int32_t lust_sys_fd_path(int32_t fd, lust_Vec *out) {
#ifdef __APPLE__
    char buf[1024]; /* MAXPATHLEN */
    if (fcntl(fd, F_GETPATH, buf) == -1) return errno;
    lust_sysio_push(out, buf, strlen(buf));
    return 0;
#else
    char link[32];
    int n = snprintf(link, sizeof link, "/proc/self/fd/%d", (int)fd);
    return lust_sys_readlink((const uint8_t *)link, (uint64_t)n, out);
#endif
}

/* The stat fields of sys.c's lust_sys_stat, for an open fd. */
int32_t lust_sys_fd_stat(int32_t fd, lust_Vec *out) {
    struct stat st;
    if (fstat(fd, &st) != 0) return errno;
    int64_t bsec = 0, bnsec = 0;
    int32_t has_btime = lust_sys_btime_fd(fd, &bsec, &bnsec);
    uint64_t f[19] = {st.st_mode, (uint64_t)st.st_size, (uint64_t)LUST_ST_MTIME(st).tv_sec, (uint64_t)LUST_ST_MTIME(st).tv_nsec, st.st_uid, st.st_gid,
                      (uint64_t)st.st_nlink, (uint64_t)st.st_ino, (uint64_t)st.st_dev, (uint64_t)LUST_ST_ATIME(st).tv_sec,
                      (uint64_t)LUST_ST_ATIME(st).tv_nsec, (uint64_t)LUST_ST_CTIME(st).tv_sec, (uint64_t)LUST_ST_CTIME(st).tv_nsec, (uint64_t)st.st_blocks,
                      (uint64_t)st.st_blksize, (uint64_t)st.st_rdev, (uint64_t)bsec, (uint64_t)bnsec, (uint64_t)has_btime};
    for (int i = 0; i < 19; i++) {
        uint8_t b[8];
        for (int k = 0; k < 8; k++) b[k] = (uint8_t)(f[i] >> (8 * k));
        lust_sysio_push(out, b, 8);
    }
    return 0;
}

/* flags: bits 0-1 access (0 O_RDONLY, 1 O_WRONLY, 2 O_RDWR), bit 2
   O_CREAT, bit 3 O_TRUNC, bit 4 O_APPEND, bit 5 O_EXCL. Always
   O_CLOEXEC, mode 0666, as std opens files on Linux. */
int32_t lust_sys_fd_open(const uint8_t *p, uint64_t len, int32_t flags) {
    char *s = malloc(len + 1);
    if (!s) lust_oom();
    memcpy(s, p, len);
    s[len] = 0;
    int f = (flags & 3) | O_CLOEXEC;
    if (flags & 4) f |= O_CREAT;
    if (flags & 8) f |= O_TRUNC;
    if (flags & 16) f |= O_APPEND;
    if (flags & 32) f |= O_EXCL;
    int fd = open(s, f, 0666);
    int e = errno;
    free(s);
    return fd < 0 ? -e : fd;
}

/* lust_sys_fd_open with std's OpenOptionsExt parts: `custom` flags
   (the access mode bits already cleared) and the creation `mode`. */
int32_t lust_sys_fd_open_ext(const uint8_t *p, uint64_t len, int32_t flags, int32_t custom, uint32_t mode) {
    char *s = malloc(len + 1);
    if (!s) lust_oom();
    memcpy(s, p, len);
    s[len] = 0;
    int f = (flags & 3) | O_CLOEXEC | custom;
    if (flags & 4) f |= O_CREAT;
    if (flags & 8) f |= O_TRUNC;
    if (flags & 16) f |= O_APPEND;
    if (flags & 32) f |= O_EXCL;
    int fd;
    do {
        fd = open(s, f, mode);
    } while (fd < 0 && errno == EINTR);
    int e = errno;
    free(s);
    return fd < 0 ? -e : fd;
}

/* Stdin: one process-wide buffer, as std's stdin. The buffer fills
   with a single read of up to 8192 bytes (std's stdin buffer size is
   also 8192 on Linux through BufReader::DEFAULT_BUF_SIZE, behind a
   line-read shim that only changes how much a terminal read asks
   for; byte streams see the same data in the same order). */
static uint8_t lust_sysio_stdin_buf[8192];
static uint64_t lust_sysio_stdin_pos, lust_sysio_stdin_cap;

int64_t lust_sys_stdin_read(uint64_t max, lust_Vec *out) {
    if (max == 0) return 0;
    if (lust_sysio_stdin_pos < lust_sysio_stdin_cap) {
        uint64_t avail = lust_sysio_stdin_cap - lust_sysio_stdin_pos;
        uint64_t n = avail < max ? avail : max;
        lust_sysio_push(out, lust_sysio_stdin_buf + lust_sysio_stdin_pos, n);
        lust_sysio_stdin_pos += n;
        return (int64_t)n;
    }
    lust_sysio_stdin_pos = lust_sysio_stdin_cap = 0;
    return lust_sys_fd_read(0, max, out);
}

int64_t lust_sys_stdin_fill(lust_Vec *out) {
    if (lust_sysio_stdin_pos >= lust_sysio_stdin_cap) {
        ssize_t n = read(0, lust_sysio_stdin_buf, sizeof lust_sysio_stdin_buf);
        if (n < 0) return -(int64_t)errno;
        lust_sysio_stdin_pos = 0;
        lust_sysio_stdin_cap = (uint64_t)n;
    }
    uint64_t avail = lust_sysio_stdin_cap - lust_sysio_stdin_pos;
    lust_sysio_push(out, lust_sysio_stdin_buf + lust_sysio_stdin_pos, avail);
    return (int64_t)avail;
}

void lust_sys_stdin_consume(uint64_t n) {
    uint64_t avail = lust_sysio_stdin_cap - lust_sysio_stdin_pos;
    lust_sysio_stdin_pos += n < avail ? n : avail;
}

/* Reads one fd that poll says is ready; appends one chunk. Returns 1
   at EOF, 0 on data, or errno. */
static int lust_sysio_read_chunk(int32_t fd, lust_Vec *out, uint8_t *tmp) {
    ssize_t n = read(fd, tmp, 65536);
    if (n < 0) return errno == EINTR ? 0 : errno;
    if (n == 0) return 1;
    lust_sysio_push(out, tmp, (uint64_t)n);
    return 0;
}

int32_t lust_sys_fd_read_both(int32_t fd1, lust_Vec *out1, int32_t fd2, lust_Vec *out2) {
    uint8_t *tmp = malloc(65536);
    if (!tmp) lust_oom();
    int err = 0, done1 = fd1 < 0, done2 = fd2 < 0;
    while (!done1 || !done2) {
        struct pollfd pf[2] = {{fd1, POLLIN, 0}, {fd2, POLLIN, 0}};
        if (done1) pf[0].fd = -1;
        if (done2) pf[1].fd = -1;
        if (poll(pf, 2, -1) < 0) {
            if (errno == EINTR) continue;
            err = errno;
            break;
        }
        for (int i = 0; i < 2; i++) {
            if (!(pf[i].revents & (POLLIN | POLLHUP | POLLERR))) continue;
            int r = lust_sysio_read_chunk(pf[i].fd, i == 0 ? out1 : out2, tmp);
            if (r == 1) {
                if (i == 0) done1 = 1; else done2 = 1;
            } else if (r != 0) {
                if (i == 0) done1 = 1; else done2 = 1;
                if (!err) err = r;
            }
        }
    }
    free(tmp);
    return err;
}

int64_t lust_sys_proc_wait(uint32_t pid, uint8_t block) {
    int st;
    for (;;) {
        pid_t r = waitpid((pid_t)pid, &st, block ? 0 : WNOHANG);
        if (r < 0 && errno == EINTR) continue;
        if (r < 0) return -(int64_t)errno;
        if (r == 0) return -2;
        return (int64_t)st;
    }
}

int32_t lust_sys_proc_kill(uint32_t pid) { return kill((pid_t)pid, SIGKILL) == 0 ? 0 : errno; }

/* glibc's PATH-searching exec with an explicit environment; declared
   here because no feature macro exposes it in this unit. Darwin has
   no execvpe: the one caller runs in a forked child about to exec,
   so swapping environ and calling execvp is the same call there
   (the PATH search then reads the child's environment, as std's
   spawn searches it). */
#ifdef __APPLE__
static int lust_execvpe(const char *file, char *const argv[], char *const envp[]) {
    environ = (char **)envp;
    return execvp(file, argv);
}
#else
int execvpe(const char *file, char *const argv[], char *const envp[]);
static int lust_execvpe(const char *file, char *const argv[], char *const envp[]) { return execvpe(file, argv, envp); }
#endif

/* Splits NUL-terminated packed strings (the argv and env formats of
   sysio.h) into a malloc'd, NULL-terminated array. The strings
   themselves are copied, so the packed bytes may be freed. */
static char **lust_sysio_split(const uint8_t *p, uint64_t len) {
    uint64_t count = 0;
    for (uint64_t i = 0; i < len; i++)
        if (p[i] == 0) count++;
    char **arr = malloc((count + 1) * sizeof *arr);
    if (!arr) lust_oom();
    uint64_t at = 0, start = 0;
    for (uint64_t i = 0; i < len; i++) {
        if (p[i] != 0) continue;
        arr[at] = malloc(i - start + 1);
        if (!arr[at]) lust_oom();
        memcpy(arr[at], p + start, i - start);
        arr[at][i - start] = 0;
        at++;
        start = i + 1;
    }
    arr[at] = NULL;
    return arr;
}

static void lust_sysio_free_split(char **arr) {
    if (!arr) return;
    for (uint64_t i = 0; arr[i]; i++) free(arr[i]);
    free(arr);
}

/* Appends one 8-byte little-endian value to the Vec. */
static void lust_sysio_push_u64(lust_Vec *out, uint64_t v) {
    uint8_t b[8];
    for (int k = 0; k < 8; k++) b[k] = (uint8_t)(v >> (8 * k));
    lust_sysio_push(out, b, 8);
}

/* Spawns `prog` with fork and execvpe, as std's Command::spawn does
   on Linux: the child's stdio is set up from the specs, then the
   working directory, then exec (with PATH search through the
   child's environment when the program has no slash). An error in
   the child before exec (chdir, dup, exec itself) travels back
   through a close-on-exec pipe and becomes the spawn error, the
   errno std reports. `stdio` packs three 2-bit specs (stdin,
   stdout, stderr) and bit 6 for a working directory; spec 0 inherit,
   1 /dev/null, 2 pipe, 3 the fd in that stream's slot of the packed
   `fds` (three 8-byte little-endian values). */
int32_t lust_sys_proc_spawn(const uint8_t *prog, uint64_t proglen, const uint8_t *args, uint64_t argslen,
                            const uint8_t *env, uint64_t envlen, const uint8_t *cwd, uint64_t cwdlen, uint32_t stdio,
                            const uint8_t *fds, uint64_t fdslen, lust_Vec *out) {
    if (argslen == 0 || envlen == 0) return EINVAL;
    char *prog_s = malloc(proglen + 1);
    if (!prog_s) lust_oom();
    memcpy(prog_s, prog, proglen);
    prog_s[proglen] = 0;
    char **argv = lust_sysio_split(args, argslen);
    char **envp = env[0] == 0 ? environ : lust_sysio_split(env + 1, envlen - 1);
    int have_cwd = (stdio >> 6) & 1;
    char *cwd_s = NULL;
    if (have_cwd) {
        cwd_s = malloc(cwdlen + 1);
        if (!cwd_s) lust_oom();
        memcpy(cwd_s, cwd, cwdlen);
        cwd_s[cwdlen] = 0;
    }
    int spec[3] = {(int)(stdio & 3), (int)((stdio >> 2) & 3), (int)((stdio >> 4) & 3)};
    int srcfd[3] = {-1, -1, -1};
    for (int i = 0; i < 3; i++) {
        if (spec[i] != 3) continue;
        if (fdslen < (uint64_t)(i + 1) * 8) return EINVAL;
        uint64_t v = 0;
        for (int k = 0; k < 8; k++) v |= (uint64_t)fds[i * 8 + k] << (8 * k);
        srcfd[i] = (int)(int64_t)v;
    }
    int pipes[3][2] = {{-1, -1}, {-1, -1}, {-1, -1}};
    int err = 0;
    for (int i = 0; i < 3 && !err; i++) {
        if (spec[i] == 2 && lust_pipe2(pipes[i], O_CLOEXEC) != 0) err = errno;
    }
    int errpipe[2] = {-1, -1};
    if (!err && lust_pipe2(errpipe, O_CLOEXEC) != 0) err = errno;
    if (err) {
        for (int i = 0; i < 3; i++) {
            if (pipes[i][0] >= 0) close(pipes[i][0]);
            if (pipes[i][1] >= 0) close(pipes[i][1]);
        }
        if (errpipe[0] >= 0) close(errpipe[0]);
        if (errpipe[1] >= 0) close(errpipe[1]);
        if (envp != environ) lust_sysio_free_split(envp);
        lust_sysio_free_split(argv);
        free(prog_s);
        free(cwd_s);
        return err;
    }
    /* Order parent and child output as rustc's line-buffered stdout
       does: text printed before the spawn is out before an
       inheriting child writes. (A partial line with no newline also
       goes out; rustc would hold it.) */
    if (spec[1] == 0 || spec[2] == 0) fflush(stdout);
    pid_t pid = fork();
    if (pid == 0) {
        /* The child: set up, report any error through errpipe, exec. */
        close(errpipe[0]);
        int target_of[3] = {0, 1, 2};
        for (int i = 0; i < 3; i++) {
            int dest = target_of[i];
            if (spec[i] == 0) continue;
            int src = srcfd[i];
            if (spec[i] == 1) {
                src = open("/dev/null", i == 0 ? O_RDONLY : O_WRONLY);
                if (src < 0) goto child_err;
            } else if (spec[i] == 2) {
                src = pipes[i][i == 0 ? 0 : 1];
            }
            if (src != dest) {
                if (dup2(src, dest) < 0) goto child_err;
            } else {
                /* The fd already is the target but is close-on-exec. */
                int fl = fcntl(src, F_GETFD);
                if (fl >= 0) fcntl(src, F_SETFD, fl & ~FD_CLOEXEC);
            }
        }
        for (int i = 0; i < 3; i++) {
            if (pipes[i][0] > 2) close(pipes[i][0]);
            if (pipes[i][1] > 2) close(pipes[i][1]);
        }
        if (have_cwd && chdir(cwd_s) != 0) goto child_err;
        signal(SIGPIPE, SIG_DFL);
        lust_execvpe(prog_s, argv, envp);
    child_err: {
            int e = errno;
            const uint8_t *p = (const uint8_t *)&e;
            uint64_t left = sizeof e;
            while (left > 0) {
                ssize_t n = write(errpipe[1], p, left);
                if (n <= 0) break;
                p += n;
                left -= (uint64_t)n;
            }
            _exit(127);
        }
    }
    int fork_err = pid < 0 ? errno : 0;
    close(errpipe[1]);
    for (int i = 0; i < 3; i++) {
        if (pipes[i][i == 0 ? 0 : 1] >= 0) close(pipes[i][i == 0 ? 0 : 1]);
    }
    if (pid < 0) {
        close(errpipe[0]);
        for (int i = 0; i < 3; i++) {
            if (pipes[i][i == 0 ? 1 : 0] >= 0) close(pipes[i][i == 0 ? 1 : 0]);
        }
        if (envp != environ) lust_sysio_free_split(envp);
        lust_sysio_free_split(argv);
        free(prog_s);
        free(cwd_s);
        return fork_err;
    }
    /* Read the error pipe: EOF means exec succeeded. */
    int child_err = 0;
    {
        uint8_t buf[sizeof(int)];
        uint64_t got = 0;
        for (;;) {
            ssize_t n = read(errpipe[0], buf + got, sizeof buf - got);
            if (n < 0 && errno == EINTR) continue;
            if (n <= 0) break;
            got += (uint64_t)n;
            if (got == sizeof buf) break;
        }
        close(errpipe[0]);
        if (got == sizeof buf) memcpy(&child_err, buf, sizeof buf);
    }
    if (envp != environ) lust_sysio_free_split(envp);
    lust_sysio_free_split(argv);
    free(prog_s);
    free(cwd_s);
    if (child_err) {
        int st;
        while (waitpid(pid, &st, 0) < 0 && errno == EINTR) {
        }
        for (int i = 0; i < 3; i++) {
            if (pipes[i][i == 0 ? 1 : 0] >= 0) close(pipes[i][i == 0 ? 1 : 0]);
        }
        return child_err;
    }
    lust_sysio_push_u64(out, (uint64_t)pid);
    for (int i = 0; i < 3; i++) lust_sysio_push_u64(out, (uint64_t)(int64_t)(spec[i] == 2 ? pipes[i][i == 0 ? 1 : 0] : -1));
    return 0;
}

int32_t lust_sys_proc_exec(const uint8_t *prog, uint64_t proglen, const uint8_t *args, uint64_t argslen,
                           const uint8_t *env, uint64_t envlen, const uint8_t *cwd, uint64_t cwdlen, uint32_t stdio,
                           const uint8_t *fds, uint64_t fdslen) {
    if (argslen == 0 || envlen == 0) return EINVAL;
    int spec[3] = {(int)(stdio & 3), (int)((stdio >> 2) & 3), (int)((stdio >> 4) & 3)};
    /* std's setup_io first: every stream's fd, then the dup2s. Our
       ends of pipes and the /dev/null fds close when this returns. */
    int theirs[3] = {-1, -1, -1}, ours[3] = {-1, -1, -1}, own[3] = {0, 0, 0};
    int err = 0;
    for (int i = 0; i < 3 && !err; i++) {
        if (spec[i] == 1) {
            theirs[i] = open("/dev/null", (i == 0 ? O_RDONLY : O_WRONLY) | O_CLOEXEC);
            if (theirs[i] < 0) err = errno;
            own[i] = 1;
        } else if (spec[i] == 2) {
            int pp[2];
            if (lust_pipe2(pp, O_CLOEXEC) != 0) {
                err = errno;
            } else {
                theirs[i] = pp[i == 0 ? 0 : 1];
                ours[i] = pp[i == 0 ? 1 : 0];
                own[i] = 1;
            }
        } else if (spec[i] == 3) {
            if (fdslen < (uint64_t)(i + 1) * 8) {
                err = EINVAL;
            } else {
                uint64_t v = 0;
                for (int k = 0; k < 8; k++) v |= (uint64_t)fds[i * 8 + k] << (8 * k);
                theirs[i] = (int)(int64_t)v;
            }
        }
    }
    for (int i = 0; i < 3 && !err; i++) {
        if (theirs[i] < 0) continue;
        while (dup2(theirs[i], i) < 0) {
            if (errno != EINTR) {
                err = errno;
                break;
            }
        }
    }
    char *prog_s = NULL, *cwd_s = NULL;
    char **argv = NULL, **envp = NULL;
    if (!err) {
        int have_cwd = (stdio >> 6) & 1;
        if (have_cwd) {
            cwd_s = malloc(cwdlen + 1);
            if (!cwd_s) lust_oom();
            memcpy(cwd_s, cwd, cwdlen);
            cwd_s[cwdlen] = 0;
            if (chdir(cwd_s) != 0) err = errno;
        }
    }
    if (!err) {
        signal(SIGPIPE, SIG_DFL);
        prog_s = malloc(proglen + 1);
        if (!prog_s) lust_oom();
        memcpy(prog_s, prog, proglen);
        prog_s[proglen] = 0;
        argv = lust_sysio_split(args, argslen);
        char **saved = environ;
        if (env[0] != 0) {
            envp = lust_sysio_split(env + 1, envlen - 1);
            environ = envp;
        }
        execvp(prog_s, argv);
        err = errno;
        environ = saved;
    }
    for (int i = 0; i < 3; i++) {
        if (own[i] && theirs[i] >= 0) close(theirs[i]);
        if (ours[i] >= 0) close(ours[i]);
    }
    if (envp) lust_sysio_free_split(envp);
    if (argv) lust_sysio_free_split(argv);
    free(prog_s);
    free(cwd_s);
    return err;
}

#endif
