// `std::os` (W-SHIM; w-cinterop3): the Unix metadata
// extension trait. The values are the stat fields the fs
// module already reads, so each method returns exactly what
// std returns for the same file. `fd` and `unix::ffi` are
// tf-adapters (F1). Not here: the Linux `st_*` spelling of
// MetadataExt, and the other `*Ext` traits.
// The items this module does not define stay with the
// compiler's std compat handling (`std_platform_compat_path`
// in src/ty/lang.rs, fx-stdos): this partial module must not
// hide `std::os::unix::fs` items that resolved before it.

/// `std::os::raw`: the C type aliases, as `core::ffi` defines them on
/// 64-bit Linux. Not here: `c_void`.
pub mod raw {
    /// `char` in C: unsigned on aarch64 Linux, signed on x86_64.
    #[cfg(target_arch = "aarch64")]
    pub type c_char = u8;
    /// `char` in C: unsigned on aarch64 Linux, signed on x86_64.
    #[cfg(not(target_arch = "aarch64"))]
    pub type c_char = i8;
    /// `signed char` in C.
    pub type c_schar = i8;
    /// `unsigned char` in C.
    pub type c_uchar = u8;
    /// `short` in C.
    pub type c_short = i16;
    /// `unsigned short` in C.
    pub type c_ushort = u16;
    /// `int` in C.
    pub type c_int = i32;
    /// `unsigned int` in C.
    pub type c_uint = u32;
    /// `long` in C (LP64).
    pub type c_long = i64;
    /// `unsigned long` in C (LP64).
    pub type c_ulong = u64;
    /// `long long` in C.
    pub type c_longlong = i64;
    /// `unsigned long long` in C.
    pub type c_ulonglong = u64;
    /// `float` in C.
    pub type c_float = f32;
    /// `double` in C.
    pub type c_double = f64;
}

/// `std::os::fd`: raw and owned Unix file descriptors, as std
/// defines them on Linux. `borrow_raw` and `from_raw_fd` are
/// `unsafe` in std; lust source cannot spell `unsafe fn`, so they
/// are safe fns here that only shipped crates may call: user code
/// that names one, or implements `FromRawFd`, rejects with L0404
/// (`UPSTREAM_UNSAFE_FNS` in src/check/platform.rs).
pub mod fd {
    use crate::fs::File;
    use crate::io;
    use core::fmt;

    /// A raw file descriptor number.
    pub type RawFd = i32;

    /// The unit value every BorrowedFd marker points at.
    static UNIT: () = ();

    /// A borrowed file descriptor.
    #[derive(Copy, Clone)]
    pub struct BorrowedFd<'fd> {
        fd: RawFd,
        marker: &'fd (),
    }

    impl<'fd> BorrowedFd<'fd> {
        /// Borrows a raw fd. The caller promises the fd stays open
        /// for `'fd` (std marks this `unsafe`; see the module note).
        pub const fn borrow_raw(fd: RawFd) -> BorrowedFd<'fd> {
            BorrowedFd { fd, marker: &UNIT }
        }
    }

    impl fmt::Debug for BorrowedFd<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("BorrowedFd").field("fd", &self.fd).finish()
        }
    }

    /// An owned file descriptor: closes on drop.
    pub struct OwnedFd {
        fd: RawFd,
    }

    impl OwnedFd {
        /// A duplicate of this fd (`F_DUPFD_CLOEXEC`, as std).
        pub fn try_clone(&self) -> io::Result<OwnedFd> {
            let n = core::intrinsics::sys_fd_dup(self.fd);
            if n < 0 {
                Err(io::Error::from_raw_os_error(-n))
            } else {
                Ok(OwnedFd { fd: n })
            }
        }
    }

    impl Drop for OwnedFd {
        fn drop(&mut self) {
            let _ = core::intrinsics::sys_fd_close(self.fd);
        }
    }

    impl fmt::Debug for OwnedFd {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("OwnedFd").field("fd", &self.fd).finish()
        }
    }

    /// A trait to borrow a file descriptor from an object.
    pub trait AsFd {
        /// Borrows the file descriptor.
        fn as_fd(&self) -> BorrowedFd<'_>;
    }

    /// A trait to extract a raw file descriptor from an object.
    pub trait AsRawFd {
        /// Extracts the raw file descriptor.
        fn as_raw_fd(&self) -> RawFd;
    }

    /// A trait to convert an object into a raw file descriptor.
    pub trait IntoRawFd {
        /// Consumes `self`, returns its fd without closing it.
        fn into_raw_fd(self) -> RawFd;
    }

    /// A trait to build an object from a raw file descriptor.
    /// std marks this trait and fn `unsafe` (module note).
    pub trait FromRawFd {
        /// Takes ownership of `fd`.
        fn from_raw_fd(fd: RawFd) -> Self;
    }

    impl AsFd for BorrowedFd<'_> {
        fn as_fd(&self) -> BorrowedFd<'_> {
            *self
        }
    }

    impl AsFd for OwnedFd {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: self.fd, marker: &UNIT }
        }
    }

    impl AsFd for File {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: self.__raw_fd(), marker: &UNIT }
        }
    }

    impl<T: AsFd + ?Sized> AsFd for &T {
        fn as_fd(&self) -> BorrowedFd<'_> {
            (**self).as_fd()
        }
    }

    impl<T: AsFd + ?Sized> AsFd for &mut T {
        fn as_fd(&self) -> BorrowedFd<'_> {
            (**self).as_fd()
        }
    }

    impl AsRawFd for BorrowedFd<'_> {
        fn as_raw_fd(&self) -> RawFd {
            self.fd
        }
    }

    impl AsRawFd for OwnedFd {
        fn as_raw_fd(&self) -> RawFd {
            self.fd
        }
    }

    impl AsRawFd for File {
        fn as_raw_fd(&self) -> RawFd {
            self.__raw_fd()
        }
    }

    impl<T: AsRawFd + ?Sized> AsRawFd for &T {
        fn as_raw_fd(&self) -> RawFd {
            (**self).as_raw_fd()
        }
    }

    impl<T: AsRawFd + ?Sized> AsRawFd for &mut T {
        fn as_raw_fd(&self) -> RawFd {
            (**self).as_raw_fd()
        }
    }

    impl IntoRawFd for OwnedFd {
        fn into_raw_fd(self) -> RawFd {
            let fd = self.fd;
            core::mem::forget(self);
            fd
        }
    }

    impl IntoRawFd for File {
        fn into_raw_fd(self) -> RawFd {
            self.__into_raw_fd()
        }
    }

    impl FromRawFd for OwnedFd {
        fn from_raw_fd(fd: RawFd) -> OwnedFd {
            OwnedFd { fd }
        }
    }

    impl FromRawFd for File {
        fn from_raw_fd(fd: RawFd) -> File {
            File::__from_raw_fd(fd)
        }
    }

    impl From<File> for OwnedFd {
        fn from(file: File) -> OwnedFd {
            OwnedFd { fd: file.__into_raw_fd() }
        }
    }

    impl io::IsTerminal for OwnedFd {
        fn is_terminal(&self) -> bool {
            io::fd_is_terminal(self.fd)
        }
    }

    impl io::IsTerminal for BorrowedFd<'_> {
        fn is_terminal(&self) -> bool {
            io::fd_is_terminal(self.fd)
        }
    }

    impl io::IsTerminal for File {
        fn is_terminal(&self) -> bool {
            io::fd_is_terminal(self.__raw_fd())
        }
    }

    impl From<OwnedFd> for crate::process::Stdio {
        fn from(fd: OwnedFd) -> crate::process::Stdio {
            crate::process::Stdio::from_fd(fd.into_raw_fd())
        }
    }

    impl From<OwnedFd> for File {
        fn from(fd: OwnedFd) -> File {
            File::__from_raw_fd(fd.into_raw_fd())
        }
    }

    // The std streams: fds 0, 1, 2 by definition, as in std.
    impl AsFd for io::Stdin {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: 0, marker: &UNIT }
        }
    }

    impl AsFd for io::Stdout {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: 1, marker: &UNIT }
        }
    }

    impl AsFd for io::Stderr {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: 2, marker: &UNIT }
        }
    }

    impl AsRawFd for io::Stdin {
        fn as_raw_fd(&self) -> RawFd {
            0
        }
    }

    impl AsRawFd for io::Stdout {
        fn as_raw_fd(&self) -> RawFd {
            1
        }
    }

    impl AsRawFd for io::Stderr {
        fn as_raw_fd(&self) -> RawFd {
            2
        }
    }
}

pub mod unix {
    /// Unix-specific extensions to `std::ffi`: `OsStr` and
    /// `OsString` as raw bytes.
    pub mod ffi {
        use crate::ffi::{os_str_from_bytes, OsStr, OsString};

        /// Unix-specific extensions to `OsStr`.
        pub trait OsStrExt {
            /// The `OsStr` of the raw bytes, as given.
            fn from_bytes(slice: &[u8]) -> &OsStr;
            /// The raw bytes of this string.
            fn as_bytes(&self) -> &[u8];
        }

        impl OsStrExt for OsStr {
            fn from_bytes(slice: &[u8]) -> &OsStr {
                os_str_from_bytes(slice)
            }
            fn as_bytes(&self) -> &[u8] {
                self.as_encoded_bytes()
            }
        }

        /// Unix-specific extensions to `OsString`.
        pub trait OsStringExt {
            /// The `OsString` of the raw bytes, as given.
            fn from_vec(vec: Vec<u8>) -> OsString;
            /// The raw bytes of this string.
            fn into_vec(self) -> Vec<u8>;
        }

        impl OsStringExt for OsString {
            fn from_vec(vec: Vec<u8>) -> OsString {
                OsString::__from_vec(vec)
            }
            fn into_vec(self) -> Vec<u8> {
                self.into_encoded_bytes()
            }
        }
    }

    /// The `std::os::unix::io` spelling of `std::os::fd`.
    pub mod io {
        pub use crate::os::fd::{AsFd, AsRawFd, BorrowedFd, FromRawFd, IntoRawFd, OwnedFd, RawFd};
    }

    /// Operating-system specific extensions.
    pub mod fs {
        use crate::fs::Metadata;

        /// Unix-specific extensions to `fs::File`: positioned reads and
        /// writes (`pread`/`pwrite`), as std's stable `FileExt` items.
        pub trait FileExt {
            /// Reads bytes at the offset; a short read is not an error.
            fn read_at(&self, buf: &mut [u8], offset: u64) -> crate::io::Result<usize>;
            /// Reads exactly enough bytes at the offset to fill the buffer.
            fn read_exact_at(&self, mut buf: &mut [u8], mut offset: u64) -> crate::io::Result<()> {
                while !buf.is_empty() {
                    match self.read_at(buf, offset) {
                        Ok(0) => break,
                        Ok(n) => {
                            let tmp = buf;
                            buf = &mut tmp[n..]; //@ std/src/os/unix/fs.rs:126:35
                            offset += n as u64;
                        }
                        Err(e) => {
                            if !e.is_interrupted() {
                                return Err(e);
                            }
                        }
                    }
                }
                if !buf.is_empty() {
                    Err(crate::io::Error::simple_message(crate::io::ErrorKind::UnexpectedEof, "failed to fill whole buffer"))
                } else {
                    Ok(())
                }
            }
            /// Writes bytes at the offset; a short write is not an error.
            fn write_at(&self, buf: &[u8], offset: u64) -> crate::io::Result<usize>;
            /// Writes the whole buffer at the offset.
            fn write_all_at(&self, mut buf: &[u8], mut offset: u64) -> crate::io::Result<()> {
                while !buf.is_empty() {
                    match self.write_at(buf, offset) {
                        Ok(0) => {
                            return Err(crate::io::Error::simple_message(crate::io::ErrorKind::WriteZero, "failed to write whole buffer"));
                        }
                        Ok(n) => {
                            buf = &buf[n..]; //@ std/src/os/unix/fs.rs:349:31
                            offset += n as u64
                        }
                        Err(e) => {
                            if !e.is_interrupted() {
                                return Err(e);
                            }
                        }
                    }
                }
                Ok(())
            }
        }

        impl FileExt for crate::fs::File {
            fn read_at(&self, buf: &mut [u8], offset: u64) -> crate::io::Result<usize> {
                let mut tmp: Vec<u8> = Vec::new();
                let n = core::intrinsics::sys_fd_pread(self.__raw_fd(), buf.len() as u64, offset as i64, &mut tmp);
                if n < 0 {
                    return Err(crate::io::Error::from_raw_os_error(-n as i32));
                }
                let n = n as usize;
                buf[..n].copy_from_slice(&tmp[..n]); //@ never
                Ok(n)
            }
            fn write_at(&self, buf: &[u8], offset: u64) -> crate::io::Result<usize> {
                let n = core::intrinsics::sys_fd_pwrite(self.__raw_fd(), buf, offset as i64);
                if n < 0 {
                    return Err(crate::io::Error::from_raw_os_error(-n as i32));
                }
                Ok(n as usize)
            }
        }

        /// Unix-specific extensions to `fs::DirBuilder`: the mode new
        /// directories get (before the umask).
        pub trait DirBuilderExt {
            fn mode(&mut self, mode: u32) -> &mut Self;
        }

        impl DirBuilderExt for crate::fs::DirBuilder {
            fn mode(&mut self, mode: u32) -> &mut crate::fs::DirBuilder {
                self.mode = mode;
                self
            }
        }

        /// Unix-specific extensions to `fs::Permissions`: the raw mode
        /// bits, as std keeps them (`mode_t`, no masking).
        pub trait PermissionsExt {
            fn mode(&self) -> u32;
            fn set_mode(&mut self, mode: u32);
            fn from_mode(mode: u32) -> Self;
        }

        /// A mode as std keeps it, a `mode_t`: `u32` on Linux, `u16` on macOS
        /// (the bits above are dropped).
        fn mode_t(mode: u32) -> u64 {
            if cfg!(target_os = "macos") { (mode as u16) as u64 } else { mode as u64 }
        }

        impl PermissionsExt for crate::fs::Permissions {
            fn mode(&self) -> u32 {
                self.mode as u32
            }
            fn set_mode(&mut self, mode: u32) {
                self.mode = mode_t(mode);
            }
            fn from_mode(mode: u32) -> crate::fs::Permissions {
                crate::fs::Permissions { mode: mode_t(mode) }
            }
        }

        /// Unix-specific extensions to `fs::Metadata`: the raw
        /// stat fields, as std exposes them.
        pub trait MetadataExt {
            /// The device number (`st_dev`).
            fn dev(&self) -> u64;
            /// The inode number (`st_ino`).
            fn ino(&self) -> u64;
            /// The file mode bits (`st_mode`).
            fn mode(&self) -> u32;
            /// The hard link count (`st_nlink`).
            fn nlink(&self) -> u64;
            /// The owner's user id (`st_uid`).
            fn uid(&self) -> u32;
            /// The owner's group id (`st_gid`).
            fn gid(&self) -> u32;
            /// The device number for special files (`st_rdev`).
            fn rdev(&self) -> u64;
            /// The size in bytes (`st_size`).
            fn size(&self) -> u64;
            /// Last access time, seconds since the epoch.
            fn atime(&self) -> i64;
            /// Last access time, the nanoseconds part.
            fn atime_nsec(&self) -> i64;
            /// Last modification time, seconds since the epoch.
            fn mtime(&self) -> i64;
            /// Last modification time, the nanoseconds part.
            fn mtime_nsec(&self) -> i64;
            /// Last status change time, seconds since the epoch.
            fn ctime(&self) -> i64;
            /// Last status change time, the nanoseconds part.
            fn ctime_nsec(&self) -> i64;
            /// The preferred block size for file system I/O.
            fn blksize(&self) -> u64;
            /// The number of 512-byte blocks allocated.
            fn blocks(&self) -> u64;
        }

        impl MetadataExt for Metadata {
            fn dev(&self) -> u64 {
                self.dev
            }
            fn ino(&self) -> u64 {
                self.ino
            }
            fn mode(&self) -> u32 {
                self.mode as u32
            }
            fn nlink(&self) -> u64 {
                self.nlink
            }
            fn uid(&self) -> u32 {
                self.uid
            }
            fn gid(&self) -> u32 {
                self.gid
            }
            fn rdev(&self) -> u64 {
                self.rdev
            }
            fn size(&self) -> u64 {
                self.len()
            }
            fn atime(&self) -> i64 {
                self.atime
            }
            fn atime_nsec(&self) -> i64 {
                self.atime_nsec
            }
            fn mtime(&self) -> i64 {
                self.mtime
            }
            fn mtime_nsec(&self) -> i64 {
                self.mtime_nsec
            }
            fn ctime(&self) -> i64 {
                self.ctime
            }
            fn ctime_nsec(&self) -> i64 {
                self.ctime_nsec
            }
            fn blksize(&self) -> u64 {
                self.blksize
            }
            fn blocks(&self) -> u64 {
                self.blocks
            }
        }

        /// Unix-specific extensions to `fs::OpenOptions`: the mode of a
        /// created file and extra `open(2)` flags, as std's.
        pub trait OpenOptionsExt {
            /// Sets the mode bits a new file is created with.
            fn mode(&mut self, mode: u32) -> &mut Self;
            /// Passes custom flags to the `flags` argument of `open`.
            fn custom_flags(&mut self, flags: i32) -> &mut Self;
        }

        impl OpenOptionsExt for crate::fs::OpenOptions {
            fn mode(&mut self, mode: u32) -> &mut crate::fs::OpenOptions {
                self.mode = mode;
                self
            }
            fn custom_flags(&mut self, flags: i32) -> &mut crate::fs::OpenOptions {
                self.custom_flags = flags;
                self
            }
        }

        /// Creates a symbolic link pointing at `original`
        /// (`symlink(2)`), as std's `os::unix::fs::symlink` does.
        pub fn symlink<P: AsRef<crate::path::Path>, Q: AsRef<crate::path::Path>>(
            original: P,
            link: Q,
        ) -> crate::io::Result<()> {
            let a = original.as_ref().as_os_str().as_encoded_bytes();
            let b = link.as_ref().as_os_str().as_encoded_bytes();
            crate::fs::status(core::intrinsics::sys_symlink(a, b))
        }
    }

    /// Unix-specific extensions to `std::process`: `exec`, and the raw
    /// wait status of an `ExitStatus`. Both traits are sealed, as std's.
    pub mod process {
        use crate::io;
        use crate::process::{Command, ExitStatus};

        mod sealed {
            pub trait Sealed {}
            impl Sealed for crate::process::Command {}
            impl Sealed for crate::process::ExitStatus {}
        }

        /// Unix-specific extensions to `process::Command` (`exec` and
        /// `arg0` here).
        pub trait CommandExt: sealed::Sealed {
            /// Replaces this process with the command's program, as
            /// std's: returns only when the exec fails, with its error.
            fn exec(&mut self) -> io::Error;
            /// Sets the child's argv[0] (the program path stays the one
            /// that runs).
            fn arg0<S>(&mut self, arg: S) -> &mut Command
            where
                S: AsRef<crate::ffi::OsStr>;
        }

        impl CommandExt for Command {
            fn exec(&mut self) -> io::Error {
                self.exec_here()
            }
            fn arg0<S>(&mut self, arg: S) -> &mut Command
            where
                S: AsRef<crate::ffi::OsStr>,
            {
                self.set_arg0(arg.as_ref());
                self
            }
        }

        /// Unix-specific extensions to `process::ExitStatus`: the raw
        /// wait status and its parts (glibc's `W*` macros).
        pub trait ExitStatusExt: sealed::Sealed {
            /// The status of a raw wait status.
            fn from_raw(raw: i32) -> Self;
            /// The signal that ended the process, if a signal did.
            fn signal(&self) -> Option<i32>;
            /// True when the process dumped core.
            fn core_dumped(&self) -> bool;
            /// The signal that stopped the process, if one did.
            fn stopped_signal(&self) -> Option<i32>;
            /// True when the process was continued from a stop.
            fn continued(&self) -> bool;
            /// The raw wait status.
            fn into_raw(self) -> i32;
        }

        impl ExitStatusExt for ExitStatus {
            fn from_raw(raw: i32) -> ExitStatus {
                ExitStatus::from_wait_status(raw)
            }
            fn signal(&self) -> Option<i32> {
                self.signal_raw()
            }
            fn core_dumped(&self) -> bool {
                self.signal_raw().is_some() && self.raw() & 0x80 != 0
            }
            fn stopped_signal(&self) -> Option<i32> {
                self.stopped_raw()
            }
            fn continued(&self) -> bool {
                self.continued_raw()
            }
            fn into_raw(self) -> i32 {
                self.raw()
            }
        }
    }
}
