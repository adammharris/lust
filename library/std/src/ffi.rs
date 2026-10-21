// `std::ffi` (W-SHIM): `OsStr` and `OsString` as on Unix, raw bytes
// with no encoding promise, plus `CStr` (tf-adapters: the borrowed
// NUL-terminated form rustix `RawDir` names return), and the `c_*` type
// aliases of 64-bit Linux (as `std::os::raw`). `CString`, `c_void`, and
// `FromBytesUntilNulError` forms are not here.
//
// `OsStr` is an unsized newtype over `[u8]` (the compiler lays it out
// as its field; shipped source may turn `&[u8]` into `&OsStr`).
// `OsString` reaches the `OsStr` methods through `Deref`, as in std.

use alloc::borrow::Cow;
use core::cmp::Ordering;
use core::fmt;
use core::ops::Deref;

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

/// Borrowed platform string: a byte slice on Unix.
pub struct OsStr {
    inner: [u8],
}

/// Owned platform string: a byte vector on Unix.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct OsString {
    inner: Vec<u8>,
}

/// The `OsStr` view of raw bytes (the bytes become the string as is).
pub(crate) fn os_str_from_bytes(bytes: &[u8]) -> &OsStr {
    bytes
}

/// The text of valid UTF-8 bytes, None for any other bytes.
pub(crate) fn bytes_to_str(bytes: &[u8]) -> Option<&str> {
    if core::intrinsics::sys_utf8_valid_up_to(bytes) == bytes.len() { Some(core::intrinsics::sys_bytes_as_str(bytes)) } else { None }
}

/// The bytes as text, each invalid sequence replaced by U+FFFD.
/// The buffer starts with the input's capacity, as std's
/// `from_utf8_lossy` allocates its owned form.
pub(crate) fn bytes_to_string_lossy(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len());
    core::intrinsics::sys_utf8_lossy(bytes, &mut out);
    out
}

/// `Debug` of platform string bytes, as std's `Utf8Chunks` debug form:
/// valid text escaped as `str` Debug escapes it, invalid bytes as
/// `\xNN`, all in double quotes.
pub(crate) fn debug_bytes(bytes: &[u8], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(s) = bytes_to_str(bytes) {
        return write!(f, "{:?}", s);
    }
    f.write_str("\"")?;
    let mut rest = bytes;
    while !rest.is_empty() {
        let valid = core::intrinsics::sys_utf8_valid_up_to(rest);
        let text = core::intrinsics::sys_bytes_as_str(&rest[..valid]);
        let quoted = format!("{:?}", text);
        f.write_str(&quoted[1..quoted.len() - 1])?;
        if valid == rest.len() {
            break;
        }
        let bad = invalid_len(&rest[valid..]);
        for k in 0..bad {
            write!(f, "\\x{:02X}", rest[valid + k])?;
        }
        rest = &rest[valid + bad..];
    }
    f.write_str("\"")
}

/// The length of the maximal invalid UTF-8 subpart at the start of
/// `bytes` (which does not start with a valid sequence): 1 to 3.
pub(crate) fn invalid_len(bytes: &[u8]) -> usize {
    let b = bytes[0];
    let (need, lo, hi) = if b >= 0xC2 && b <= 0xDF {
        (2, 0x80, 0xBF)
    } else if b == 0xE0 {
        (3, 0xA0, 0xBF)
    } else if b == 0xED {
        (3, 0x80, 0x9F)
    } else if b >= 0xE1 && b <= 0xEF {
        (3, 0x80, 0xBF)
    } else if b == 0xF0 {
        (4, 0x90, 0xBF)
    } else if b == 0xF4 {
        (4, 0x80, 0x8F)
    } else if b >= 0xF1 && b <= 0xF3 {
        (4, 0x80, 0xBF)
    } else {
        return 1;
    };
    let mut k = 1;
    while k < need && k < bytes.len() {
        let c = bytes[k];
        let (l, h) = if k == 1 { (lo, hi) } else { (0x80, 0xBF) };
        if c < l || c > h {
            return k;
        }
        k += 1;
    }
    k
}

impl OsStr {
    /// Coerces into an `OsStr` slice.
    pub fn new<S: AsRef<OsStr> + ?Sized>(s: &S) -> &OsStr {
        s.as_ref()
    }

    /// The string as `&str` if it is valid Unicode.
    pub fn to_str(&self) -> Option<&str> {
        bytes_to_str(&self.inner)
    }

    /// The string as text, borrowed when it is valid Unicode, else
    /// owned with each invalid sequence replaced by U+FFFD.
    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        match bytes_to_str(&self.inner) {
            Some(s) => Cow::Borrowed(s),
            None => Cow::Owned(bytes_to_string_lossy(&self.inner)),
        }
    }

    /// An owned copy.
    pub fn to_os_string(&self) -> OsString {
        OsString { inner: self.inner.to_vec() }
    }

    /// True for the empty string.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// The length in bytes.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// The underlying bytes.
    pub fn as_encoded_bytes(&self) -> &[u8] {
        &self.inner
    }

    /// ASCII case-insensitive equality.
    pub fn eq_ignore_ascii_case<S: AsRef<OsStr>>(&self, other: S) -> bool {
        let a = &self.inner;
        let b = &other.as_ref().inner;
        if a.len() != b.len() {
            return false;
        }
        for i in 0..a.len() {
            if ascii_lower(a[i]) != ascii_lower(b[i]) {
                return false;
            }
        }
        true
    }

    /// A copy with ASCII letters lowercased.
    pub fn to_ascii_lowercase(&self) -> OsString {
        let mut v = self.inner.to_vec();
        for i in 0..v.len() {
            v[i] = ascii_lower(v[i]);
        }
        OsString { inner: v }
    }

    /// A copy with ASCII letters uppercased.
    pub fn to_ascii_uppercase(&self) -> OsString {
        let mut v = self.inner.to_vec();
        for i in 0..v.len() {
            let b = v[i];
            if b >= b'a' && b <= b'z' {
                v[i] = b - 32;
            }
        }
        OsString { inner: v }
    }
}

fn ascii_lower(b: u8) -> u8 {
    if b >= b'A' && b <= b'Z' { b + 32 } else { b }
}

impl OsString {
    /// An empty `OsString`.
    pub fn new() -> OsString {
        OsString { inner: Vec::new() }
    }

    /// An empty `OsString` with room for `capacity` bytes.
    pub fn with_capacity(capacity: usize) -> OsString {
        OsString { inner: Vec::with_capacity(capacity) }
    }

    /// The `OsString` of the bytes, as given.
    pub(crate) fn __from_vec(inner: Vec<u8>) -> OsString {
        OsString { inner }
    }

    /// The string as a `String` if it is valid Unicode, else itself.
    pub fn into_string(self) -> Result<String, OsString> {
        if core::intrinsics::sys_utf8_valid_up_to(&self.inner) == self.inner.len() {
            Ok(core::intrinsics::sys_string_from_utf8_unchecked(self.inner))
        } else {
            Err(self)
        }
    }

    /// The bytes.
    pub fn into_encoded_bytes(self) -> Vec<u8> {
        self.inner
    }

    /// Appends a platform string.
    pub fn push<T: AsRef<OsStr>>(&mut self, s: T) {
        let s: &OsStr = s.as_ref();
        self.inner.extend_from_slice(&s.inner);
    }

    /// The borrowed `OsStr`.
    pub fn as_os_str(&self) -> &OsStr {
        os_str_from_bytes(&self.inner)
    }

    /// Removes the contents, keeping the buffer.
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// The buffer capacity in bytes.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Shortens the string to `len` bytes.
    pub(crate) fn truncate(&mut self, len: usize) {
        self.inner.truncate(len);
    }
}

impl ToOwned for OsStr {
    type Owned = OsString;

    fn to_owned(&self) -> OsString {
        self.to_os_string()
    }

    fn clone_into(&self, target: &mut OsString) {
        target.clear();
        target.push(self);
    }
}

impl fmt::Debug for OsStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_bytes(&self.inner, f)
    }
}

impl fmt::Debug for OsString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_bytes(&self.inner, f)
    }
}

impl AsRef<OsStr> for OsStr {
    fn as_ref(&self) -> &OsStr {
        self
    }
}

impl AsRef<OsStr> for OsString {
    fn as_ref(&self) -> &OsStr {
        os_str_from_bytes(&self.inner)
    }
}

impl AsRef<OsStr> for str {
    fn as_ref(&self) -> &OsStr {
        os_str_from_bytes(core::intrinsics::sys_str_as_bytes(self))
    }
}

impl AsRef<OsStr> for String {
    fn as_ref(&self) -> &OsStr {
        os_str_from_bytes(self.as_bytes())
    }
}

impl From<String> for OsString {
    fn from(s: String) -> OsString {
        OsString { inner: s.into_bytes() }
    }
}

impl<T: ?Sized + AsRef<OsStr>> From<&T> for OsString {
    /// Copies any value implementing `AsRef<OsStr>` into a newly allocated
    /// `OsString`.
    fn from(s: &T) -> OsString {
        s.as_ref().to_os_string()
    }
}

impl PartialEq for OsStr {
    fn eq(&self, other: &OsStr) -> bool {
        self.inner == other.inner
    }
}

impl Eq for OsStr {}

impl PartialEq<str> for OsStr {
    fn eq(&self, other: &str) -> bool {
        &self.inner == core::intrinsics::sys_str_as_bytes(other)
    }
}

impl PartialEq<OsStr> for str {
    fn eq(&self, other: &OsStr) -> bool {
        core::intrinsics::sys_str_as_bytes(self) == &other.inner
    }
}

impl PartialEq<str> for OsString {
    fn eq(&self, other: &str) -> bool {
        self.inner.as_slice() == core::intrinsics::sys_str_as_bytes(other)
    }
}

impl PartialEq<&str> for OsString {
    fn eq(&self, other: &&str) -> bool {
        self.inner.as_slice() == core::intrinsics::sys_str_as_bytes(*other)
    }
}

impl PartialEq<OsString> for str {
    fn eq(&self, other: &OsString) -> bool {
        core::intrinsics::sys_str_as_bytes(self) == other.inner.as_slice()
    }
}

impl PartialEq<OsString> for &str {
    fn eq(&self, other: &OsString) -> bool {
        core::intrinsics::sys_str_as_bytes(*self) == other.inner.as_slice()
    }
}

impl PartialEq<OsStr> for OsString {
    fn eq(&self, other: &OsStr) -> bool {
        self.inner.as_slice() == &other.inner
    }
}

impl PartialEq<OsString> for OsStr {
    fn eq(&self, other: &OsString) -> bool {
        &self.inner == other.inner.as_slice()
    }
}

impl PartialOrd for OsStr {
    fn partial_cmp(&self, other: &OsStr) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OsStr {
    fn cmp(&self, other: &OsStr) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl Deref for OsString {
    type Target = OsStr;
    fn deref(&self) -> &OsStr {
        os_str_from_bytes(&self.inner)
    }
}

/// Borrowed C string: bytes with exactly one NUL, at the end. An
/// unsized newtype over `[u8]`, like `OsStr`.
pub struct CStr {
    inner: [u8],
}

/// The `CStr` view of bytes that end with their only NUL.
pub(crate) fn c_str_from_bytes(bytes: &[u8]) -> &CStr {
    bytes
}

/// An error from `CStr::from_bytes_with_nul`, as std's enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FromBytesWithNulError {
    /// A NUL byte before the end of the input.
    InteriorNul { position: usize },
    /// No NUL byte at the end of the input.
    NotNulTerminated,
}

impl fmt::Display for FromBytesWithNulError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FromBytesWithNulError::InteriorNul { position } => {
                write!(f, "data provided contains an interior nul byte at byte position {}", position)
            }
            FromBytesWithNulError::NotNulTerminated => f.write_str("data provided is not nul terminated"),
        }
    }
}

impl CStr {
    /// The `CStr` of `bytes` when the last byte is its only NUL.
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<&CStr, FromBytesWithNulError> {
        // std finds the first NUL: at the end is Ok, earlier is an
        // interior NUL, and no NUL at all is not terminated.
        for i in 0..bytes.len() {
            if bytes[i] == 0 {
                if i == bytes.len() - 1 {
                    return Ok(c_str_from_bytes(bytes));
                }
                return Err(FromBytesWithNulError::InteriorNul { position: i });
            }
        }
        Err(FromBytesWithNulError::NotNulTerminated)
    }

    /// The bytes without the final NUL.
    pub fn to_bytes(&self) -> &[u8] {
        &self.inner[..self.inner.len() - 1]
    }

    /// The bytes with the final NUL.
    pub fn to_bytes_with_nul(&self) -> &[u8] {
        &self.inner
    }

    /// True for the empty string (only the NUL).
    pub fn is_empty(&self) -> bool {
        self.inner.len() == 1
    }

    /// The bytes without the final NUL as text, as std's `to_str`
    /// (`str::from_utf8` of `to_bytes`).
    pub fn to_str(&self) -> Result<&str, core::str::Utf8Error> {
        core::str::from_utf8(self.to_bytes())
    }

    /// The bytes as text, borrowed when valid, else lossy owned.
    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        match bytes_to_str(self.to_bytes()) {
            Some(s) => Cow::Borrowed(s),
            None => Cow::Owned(bytes_to_string_lossy(self.to_bytes())),
        }
    }
}

impl fmt::Debug for CStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        __lust_bytestr_debug(self.to_bytes(), f)
    }
}

/// std's `ByteStr` Debug, which `CStr` and `CString` use (and
/// `process::Command` and `os::unix::net::SocketAddr` print through):
/// quoted; NUL as `\0`; an ASCII char as `u8::escape_ascii` gives it
/// (`\t`, `\r`, `\n`, `\\`, `\'`, `\"`, other controls `\xNN`); other
/// valid text by `char::escape_debug`; invalid bytes as `\xNN`.
pub fn __lust_bytestr_debug(bytes: &[u8], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str("\"")?;
    let mut rest = bytes;
    while !rest.is_empty() {
        let valid = core::intrinsics::sys_utf8_valid_up_to(rest);
        let text = core::intrinsics::sys_bytes_as_str(&rest[..valid]);
        for c in text.chars() {
            match c {
                '\0' => f.write_str("\\0")?,
                '\t' => f.write_str("\\t")?,
                '\r' => f.write_str("\\r")?,
                '\n' => f.write_str("\\n")?,
                '\\' => f.write_str("\\\\")?,
                '\'' => f.write_str("\\'")?,
                '"' => f.write_str("\\\"")?,
                ' '..='~' => write!(f, "{}", c)?,
                '\x01'..='\x7f' => write!(f, "\\x{:02x}", c as u32)?,
                _ => {
                    // `char::escape_debug`: the char's Debug without
                    // its quotes (no quote char is above U+007F).
                    let d = format!("{:?}", c);
                    f.write_str(&d[1..d.len() - 1])?;
                }
            }
        }
        if valid == rest.len() {
            break;
        }
        let bad = invalid_len(&rest[valid..]);
        for k in 0..bad {
            write!(f, "\\x{:02x}", rest[valid + k])?;
        }
        rest = &rest[valid + bad..];
    }
    f.write_str("\"")
}

impl PartialEq for CStr {
    fn eq(&self, other: &CStr) -> bool {
        self.inner == other.inner
    }
}

impl Eq for CStr {}
