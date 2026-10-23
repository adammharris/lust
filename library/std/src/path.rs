// `std::path` (W-SHIM): `Path` and `PathBuf` as on Unix.
//
// `Path` is an unsized newtype over `OsStr` (so over `[u8]`), as in
// std. Components parse exactly as std's `Components` does on Unix: no
// prefixes, `/` is the only separator, repeated separators and inner
// `.` components vanish, a leading `.` stays as `CurDir`. Comparison,
// ordering, and hashing go through the components, as std's do.
// The parser works on byte offsets into the path (std uses pointer
// arithmetic for `set_extension`; offsets give the same answers).

use alloc::borrow::Cow;
use crate::ffi::{OsStr, OsString, os_str_from_bytes};
use core::cmp::Ordering;
use core::fmt;
use core::ops::Deref;

/// The separator of path components on Unix.
pub const MAIN_SEPARATOR: char = '/';
/// `MAIN_SEPARATOR` as a string.
pub const MAIN_SEPARATOR_STR: &str = "/";

/// True for the separator byte (`/` on Unix).
pub fn is_separator(c: char) -> bool {
    c == '/'
}

/// A slice of a path: an unsized type, always behind a reference.
pub struct Path {
    inner: OsStr,
}

/// An owned, mutable path.
pub struct PathBuf {
    inner: OsString,
}

/// The `Path` view of raw bytes.
fn path_from_bytes(bytes: &[u8]) -> &Path {
    bytes
}

/// A Windows path prefix. Unix paths never have one, so no value of
/// this type exists; it is here so that matches on `Component` are
/// exhaustive as in std.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PrefixComponent<'a> {
    raw: &'a OsStr,
}

impl<'a> PrefixComponent<'a> {
    /// The raw prefix text.
    pub fn as_os_str(&self) -> &'a OsStr {
        self.raw
    }
}

/// One component of a path.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Component<'a> {
    Prefix(PrefixComponent<'a>),
    RootDir,
    CurDir,
    ParentDir,
    Normal(&'a OsStr),
}

impl<'a> Component<'a> {
    /// The component's text: `/`, `.`, `..`, or the name.
    pub fn as_os_str(self) -> &'a OsStr {
        match self {
            Component::Prefix(p) => p.as_os_str(),
            Component::RootDir => OsStr::new("/"),
            Component::CurDir => OsStr::new("."),
            Component::ParentDir => OsStr::new(".."),
            Component::Normal(path) => path,
        }
    }
}

impl AsRef<OsStr> for Component<'_> {
    fn as_ref(&self) -> &OsStr {
        self.as_os_str()
    }
}

impl AsRef<Path> for Component<'_> {
    fn as_ref(&self) -> &Path {
        Path::new(self.as_os_str())
    }
}

/// Parser state of one end of `Components`, in std's order (the
/// iterator is done when the front state passes the back state).
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum State {
    Prefix,
    StartDir,
    Body,
    Done,
}

/// What a parsed piece of the body is (a `Component` without its text).
#[derive(Copy, Clone, PartialEq)]
enum Piece {
    Root,
    Cur,
    Parent,
    Normal,
}

/// The iterator over the components of a path.
#[derive(Clone)]
pub struct Components<'a> {
    /// The whole path; `start..end` is the part not yet iterated.
    path: &'a [u8],
    start: usize,
    end: usize,
    has_physical_root: bool,
    front: State,
    back: State,
}

impl<'a> Components<'a> {
    fn new(path: &'a [u8]) -> Components<'a> {
        Components {
            path,
            start: 0,
            end: path.len(),
            has_physical_root: !path.is_empty() && path[0] == b'/',
            front: State::Prefix,
            back: State::Body,
        }
    }

    fn rest(&self) -> &'a [u8] {
        &self.path[self.start..self.end]
    }

    fn finished(&self) -> bool {
        self.front == State::Done || self.back == State::Done || self.front > self.back
    }

    /// True when the path starts with a `.` component (only without a root).
    fn include_cur_dir(&self) -> bool {
        if self.has_physical_root {
            return false;
        }
        let rest = self.rest();
        !rest.is_empty() && rest[0] == b'.' && (rest.len() == 1 || rest[1] == b'/')
    }

    /// Bytes before the body: the root and a leading `.`, while the
    /// front has not passed them.
    fn len_before_body(&self) -> usize {
        let root = if self.front <= State::StartDir && self.has_physical_root { 1 } else { 0 };
        let cur_dir = if self.front <= State::StartDir && self.include_cur_dir() { 1 } else { 0 };
        root + cur_dir
    }

    /// The kind of one body component's text: None for `.` and empty.
    fn parse_single(comp: &[u8]) -> Option<Piece> {
        if comp.is_empty() || (comp.len() == 1 && comp[0] == b'.') {
            None
        } else if comp.len() == 2 && comp[0] == b'.' && comp[1] == b'.' {
            Some(Piece::Parent)
        } else {
            Some(Piece::Normal)
        }
    }

    /// The next body component from the front: bytes consumed, then
    /// the component's kind and start offset.
    fn parse_next(&self) -> (usize, Option<Piece>, usize) {
        let rest = self.rest();
        let mut i = 0;
        while i < rest.len() && rest[i] != b'/' {
            i += 1;
        }
        let extra = if i < rest.len() { 1 } else { 0 };
        (i + extra, Components::parse_single(&rest[..i]), self.start)
    }

    /// The next body component from the back: bytes consumed, then the
    /// component's kind and start offset.
    fn parse_next_back(&self) -> (usize, Option<Piece>, usize) {
        let lo = self.start + self.len_before_body();
        let mut i = self.end;
        while i > lo && self.path[i - 1] != b'/' {
            i -= 1;
        }
        let extra = if i > lo { 1 } else { 0 };
        (self.end - i + extra, Components::parse_single(&self.path[i..self.end]), i)
    }

    fn component(&self, piece: Piece, at: usize, len: usize) -> Component<'a> {
        match piece {
            Piece::Root => Component::RootDir,
            Piece::Cur => Component::CurDir,
            Piece::Parent => Component::ParentDir,
            Piece::Normal => Component::Normal(os_str_from_bytes(&self.path[at..at + len])),
        }
    }

    fn trim_left(&mut self) {
        while self.start < self.end {
            let (size, comp, _) = self.parse_next();
            if comp.is_some() {
                return;
            }
            self.start += size;
        }
    }

    fn trim_right(&mut self) {
        while self.end - self.start > self.len_before_body() {
            let (size, comp, _) = self.parse_next_back();
            if comp.is_some() {
                return;
            }
            self.end -= size;
        }
    }

    /// The rest of the path as a `Path`, without trailing separators
    /// or `.` components at either end of the body.
    pub fn as_path(&self) -> &'a Path {
        let mut comps = self.clone();
        if comps.front == State::Body {
            comps.trim_left();
        }
        if comps.back == State::Body {
            comps.trim_right();
        }
        path_from_bytes(comps.rest())
    }

    /// `next_back`, plus the component's byte offset and length in the
    /// whole path (for `set_extension`).
    fn next_back_range(&mut self) -> Option<(Component<'a>, usize, usize)> {
        while !self.finished() {
            match self.back {
                State::Body if self.end - self.start > self.len_before_body() => {
                    let (size, comp, at) = self.parse_next_back();
                    self.end -= size;
                    if let Some(piece) = comp {
                        let n = self.comp_len(at);
                        return Some((self.component(piece, at, n), at, n));
                    }
                }
                State::Body => self.back = State::StartDir,
                State::StartDir => {
                    self.back = State::Prefix;
                    if self.has_physical_root {
                        self.end -= 1;
                        return Some((Component::RootDir, self.end, 1));
                    } else if self.include_cur_dir() {
                        self.end -= 1;
                        return Some((Component::CurDir, self.end, 1));
                    }
                }
                State::Prefix => {
                    self.back = State::Done;
                    return None;
                }
                State::Done => return None,
            }
        }
        None
    }

    /// The length of the body component that starts at `at`.
    fn comp_len(&self, at: usize) -> usize {
        let mut i = at;
        while i < self.path.len() && self.path[i] != b'/' {
            i += 1;
        }
        i - at
    }
}

impl<'a> Iterator for Components<'a> {
    type Item = Component<'a>;

    fn next(&mut self) -> Option<Component<'a>> {
        while !self.finished() {
            match self.front {
                State::Prefix => self.front = State::StartDir,
                State::StartDir => {
                    self.front = State::Body;
                    if self.has_physical_root {
                        self.start += 1;
                        return Some(Component::RootDir);
                    } else if self.include_cur_dir() {
                        self.start += 1;
                        return Some(Component::CurDir);
                    }
                }
                State::Body if self.start < self.end => {
                    let (size, comp, at) = self.parse_next();
                    self.start += size;
                    if let Some(piece) = comp {
                        let n = self.comp_len(at);
                        return Some(self.component(piece, at, n));
                    }
                }
                State::Body => self.front = State::Done,
                State::Done => return None,
            }
        }
        None
    }
}

// Lust has no user `DoubleEndedIterator` impls yet: `next_back` is
// inherent (the same method call, as the trait is in the prelude), and
// `rev()` is not available.
impl<'a> Components<'a> {
    /// The next component from the back.
    pub fn next_back(&mut self) -> Option<Component<'a>> {
        match self.next_back_range() {
            Some((c, _, _)) => Some(c),
            None => None,
        }
    }
}

impl PartialEq for Components<'_> {
    fn eq(&self, other: &Components<'_>) -> bool {
        // From the back, as std (paths often share long prefixes).
        let (mut a, mut b) = (self.clone(), other.clone());
        loop {
            match a.next_back() {
                None => return b.next_back().is_none(),
                Some(x) => match b.next_back() {
                    Some(y) if x == y => {}
                    _ => return false,
                },
            }
        }
    }
}

impl Eq for Components<'_> {}

impl PartialOrd for Components<'_> {
    fn partial_cmp(&self, other: &Components<'_>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Components<'_> {
    fn cmp(&self, other: &Components<'_>) -> Ordering {
        let (mut a, mut b) = (self.clone(), other.clone());
        loop {
            let x = match a.next() {
                None => return if b.next().is_none() { Ordering::Equal } else { Ordering::Less },
                Some(x) => x,
            };
            let y = match b.next() {
                None => return Ordering::Greater,
                Some(y) => y,
            };
            match component_cmp(x, y) {
                Ordering::Equal => {}
                o => return o,
            }
        }
    }
}

impl AsRef<Path> for Components<'_> {
    fn as_ref(&self) -> &Path {
        self.as_path()
    }
}

impl AsRef<OsStr> for Components<'_> {
    fn as_ref(&self) -> &OsStr {
        self.as_path().as_os_str()
    }
}

impl fmt::Debug for Components<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Components").field(&DebugComponents(self.as_path())).finish()
    }
}

/// The component list of a path, for `Components` Debug.
struct DebugComponents<'a>(&'a Path);

impl fmt::Debug for DebugComponents<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut list = f.debug_list();
        for c in self.0.components() {
            list.entry(&c);
        }
        list.finish()
    }
}

/// The iterator over the components of a path as `OsStr` slices.
#[derive(Clone)]
pub struct Iter<'a> {
    inner: Components<'a>,
}

impl<'a> Iter<'a> {
    /// The rest of the path as a `Path`.
    pub fn as_path(&self) -> &'a Path {
        self.inner.as_path()
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a OsStr;

    fn next(&mut self) -> Option<&'a OsStr> {
        match self.inner.next() {
            Some(c) => Some(c.as_os_str()),
            None => None,
        }
    }
}

impl<'a> Iter<'a> {
    /// The next component from the back.
    pub fn next_back(&mut self) -> Option<&'a OsStr> {
        match self.inner.next_back() {
            Some(c) => Some(c.as_os_str()),
            None => None,
        }
    }
}

impl AsRef<Path> for Iter<'_> {
    fn as_ref(&self) -> &Path {
        self.as_path()
    }
}

impl AsRef<OsStr> for Iter<'_> {
    fn as_ref(&self) -> &OsStr {
        self.as_path().as_os_str()
    }
}

impl fmt::Debug for Iter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter").field(&DebugIter(self.as_path())).finish()
    }
}

/// The `OsStr` list of a path, for `Iter` Debug.
struct DebugIter<'a>(&'a Path);

impl fmt::Debug for DebugIter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut list = f.debug_list();
        for c in self.0.iter() {
            list.entry(&c);
        }
        list.finish()
    }
}

/// The iterator over a path and its ancestors (`Path::ancestors`).
#[derive(Copy, Clone)]
pub struct Ancestors<'a> {
    next: Option<&'a Path>,
}

impl fmt::Debug for Ancestors<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ancestors").field("next", &self.next).finish()
    }
}

impl<'a> Iterator for Ancestors<'a> {
    type Item = &'a Path;

    fn next(&mut self) -> Option<&'a Path> {
        let next = self.next;
        self.next = match next {
            Some(p) => p.parent(),
            None => None,
        };
        next
    }
}

/// `Ord` of two components as std's derive orders them: by variant,
/// then by name for two `Normal` ones.
fn component_cmp(a: Component<'_>, b: Component<'_>) -> Ordering {
    match (a, b) {
        (Component::Normal(x), Component::Normal(y)) => x.as_encoded_bytes().cmp(y.as_encoded_bytes()),
        _ => component_rank(a).cmp(&component_rank(b)),
    }
}

fn component_rank(c: Component<'_>) -> u8 {
    match c {
        Component::Prefix(_) => 0,
        Component::RootDir => 1,
        Component::CurDir => 2,
        Component::ParentDir => 3,
        Component::Normal(_) => 4,
    }
}

/// The error of `Path::strip_prefix` when the prefix does not match.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StripPrefixError(());

impl fmt::Display for StripPrefixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("prefix not found")
    }
}

/// `iter` after `prefix`, when `prefix` is a prefix of it (std's
/// `iter_after`).
fn iter_after<'a>(mut iter: Components<'a>, mut prefix: Components<'_>) -> Option<Components<'a>> {
    loop {
        let mut iter_next = iter.clone();
        let x = iter_next.next();
        match prefix.next() {
            None => return Some(iter),
            Some(y) => match x {
                Some(x) if x == y => {}
                _ => return None,
            },
        }
        iter = iter_next;
    }
}

/// `iter_after` from the back.
fn iter_after_back<'a>(mut iter: Components<'a>, mut suffix: Components<'_>) -> Option<Components<'a>> {
    loop {
        let mut iter_next = iter.clone();
        let x = iter_next.next_back();
        match suffix.next_back() {
            None => return Some(iter),
            Some(y) => match x {
                Some(x) if x == y => {}
                _ => return None,
            },
        }
        iter = iter_next;
    }
}

/// A file name split at its last dot: (before, after). `..` and names
/// that start with their only dot have no extension.
fn rsplit_file_at_dot(file: &OsStr) -> (Option<&OsStr>, Option<&OsStr>) {
    let bytes = file.as_encoded_bytes();
    if bytes.len() == 2 && bytes[0] == b'.' && bytes[1] == b'.' {
        return (Some(file), None);
    }
    let mut i = bytes.len();
    while i > 0 && bytes[i - 1] != b'.' {
        i -= 1;
    }
    if i == 0 {
        return (None, Some(file));
    }
    if i == 1 {
        return (Some(file), None);
    }
    (Some(os_str_from_bytes(&bytes[..i - 1])), Some(os_str_from_bytes(&bytes[i..])))
}

impl Path {
    /// Wraps a string slice as a path slice.
    pub fn new<S: AsRef<OsStr> + ?Sized>(s: &S) -> &Path {
        let os: &OsStr = s.as_ref();
        os
    }

    fn bytes(&self) -> &[u8] {
        self.inner.as_encoded_bytes()
    }

    /// The path as an `OsStr`.
    pub fn as_os_str(&self) -> &OsStr {
        &self.inner
    }

    /// The path as `&str` if it is valid Unicode.
    pub fn to_str(&self) -> Option<&str> {
        self.inner.to_str()
    }

    /// The path as text, borrowed when it is valid Unicode, else
    /// owned with each invalid sequence replaced by U+FFFD.
    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        self.inner.to_string_lossy()
    }

    /// An owned copy.
    pub fn to_path_buf(&self) -> PathBuf {
        PathBuf { inner: self.inner.to_os_string() }
    }

    /// True for a path with a root (it starts with `/`).
    pub fn is_absolute(&self) -> bool {
        self.has_root()
    }

    /// True for a path without a root.
    pub fn is_relative(&self) -> bool {
        !self.is_absolute()
    }

    /// True for a path that starts with `/`.
    pub fn has_root(&self) -> bool {
        self.components().has_physical_root
    }

    /// The path without its last component, None for a root or empty path.
    pub fn parent(&self) -> Option<&Path> {
        let mut comps = self.components();
        match comps.next_back() {
            Some(Component::Normal(_)) | Some(Component::CurDir) | Some(Component::ParentDir) => Some(comps.as_path()),
            _ => None,
        }
    }

    /// The path, then each parent in turn.
    pub fn ancestors(&self) -> Ancestors<'_> {
        Ancestors { next: Some(self) }
    }

    /// The last component if it is a normal name.
    pub fn file_name(&self) -> Option<&OsStr> {
        match self.components().next_back() {
            Some(Component::Normal(p)) => Some(p),
            _ => None,
        }
    }

    /// The path after `base`, when `base` is a prefix of it.
    pub fn strip_prefix<P: AsRef<Path>>(&self, base: P) -> Result<&Path, StripPrefixError> {
        match iter_after(self.components(), base.as_ref().components()) {
            Some(c) => Ok(c.as_path()),
            None => Err(StripPrefixError(())),
        }
    }

    /// True when `base` is a component prefix of this path.
    pub fn starts_with<P: AsRef<Path>>(&self, base: P) -> bool {
        iter_after(self.components(), base.as_ref().components()).is_some()
    }

    /// True when `child` is a component suffix of this path.
    pub fn ends_with<P: AsRef<Path>>(&self, child: P) -> bool {
        iter_after_back(self.components(), child.as_ref().components()).is_some()
    }

    /// The file name without its extension.
    pub fn file_stem(&self) -> Option<&OsStr> {
        let (before, after) = rsplit_file_at_dot(self.file_name()?);
        if before.is_some() { before } else { after }
    }

    /// The file name without anything after its first dot.
    pub fn file_prefix(&self) -> Option<&OsStr> {
        let name = self.file_name()?;
        let bytes = name.as_encoded_bytes();
        if bytes.len() == 2 && bytes[0] == b'.' && bytes[1] == b'.' {
            return Some(name);
        }
        let mut i = 1;
        while i < bytes.len() && bytes[i] != b'.' {
            i += 1;
        }
        Some(os_str_from_bytes(&bytes[..i.min(bytes.len())]))
    }

    /// The extension of the file name.
    pub fn extension(&self) -> Option<&OsStr> {
        let (before, after) = rsplit_file_at_dot(self.file_name()?);
        if before.is_some() { after } else { None }
    }

    /// The path with `path` pushed onto it (`PathBuf::push`).
    pub fn join<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        let mut buf = self.to_path_buf();
        buf.push(path);
        buf
    }

    /// The path with its file name replaced (`PathBuf::set_file_name`).
    pub fn with_file_name<S: AsRef<OsStr>>(&self, file_name: S) -> PathBuf {
        let mut buf = self.to_path_buf();
        buf.set_file_name(file_name);
        buf
    }

    /// The path with its extension replaced (`PathBuf::set_extension`).
    pub fn with_extension<S: AsRef<OsStr>>(&self, extension: S) -> PathBuf {
        let extension = extension.as_ref();
        let bytes = self.bytes();
        // As std: keep the dot of an old extension, then set the new one.
        let keep = match self.extension() {
            None => bytes.len(),
            Some(previous) => bytes.len() - previous.len(),
        };
        let mut new_path = PathBuf::new();
        new_path.inner.push(os_str_from_bytes(&bytes[..keep]));
        new_path.set_extension(extension);
        new_path
    }

    /// The components of the path.
    pub fn components(&self) -> Components<'_> {
        Components::new(self.bytes())
    }

    /// The components of the path as `OsStr` slices.
    pub fn iter(&self) -> Iter<'_> {
        Iter { inner: self.components() }
    }

    /// True when the path exists (following symlinks); any error is false.
    pub fn exists(&self) -> bool {
        match crate::fs::metadata(self) {
            Ok(_) => true,
            Err(_) => false,
        }
    }

    /// `fs::exists`: errors other than NotFound are returned.
    pub fn try_exists(&self) -> crate::io::Result<bool> {
        crate::fs::exists(self)
    }

    /// True for a path to a regular file (following symlinks).
    pub fn is_file(&self) -> bool {
        match crate::fs::metadata(self) {
            Ok(m) => m.is_file(),
            Err(_) => false,
        }
    }

    /// True for a path to a directory (following symlinks).
    pub fn is_dir(&self) -> bool {
        match crate::fs::metadata(self) {
            Ok(m) => m.is_dir(),
            Err(_) => false,
        }
    }

    /// True for a path that is a symbolic link.
    pub fn is_symlink(&self) -> bool {
        match crate::fs::symlink_metadata(self) {
            Ok(m) => m.is_symlink(),
            Err(_) => false,
        }
    }

    /// `fs::metadata` of this path.
    pub fn metadata(&self) -> crate::io::Result<crate::fs::Metadata> {
        crate::fs::metadata(self)
    }

    /// `fs::symlink_metadata` of this path.
    pub fn symlink_metadata(&self) -> crate::io::Result<crate::fs::Metadata> {
        crate::fs::symlink_metadata(self)
    }

    /// `fs::read_dir` of this path.
    pub fn read_dir(&self) -> crate::io::Result<crate::fs::ReadDir> {
        crate::fs::read_dir(self)
    }

    /// `fs::canonicalize` of this path.
    pub fn canonicalize(&self) -> crate::io::Result<PathBuf> {
        crate::fs::canonicalize(self)
    }

    /// `fs::read_link` of this path.
    pub fn read_link(&self) -> crate::io::Result<PathBuf> {
        crate::fs::read_link(self)
    }

    /// A value that formats the path with `{}` (invalid UTF-8 becomes U+FFFD).
    pub fn display(&self) -> Display<'_> {
        Display { path: self }
    }
}

/// Formats a path for display (`Path::display`).
pub struct Display<'a> {
    path: &'a Path,
}

impl fmt::Debug for Display<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.path)
    }
}

impl fmt::Display for Display<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // As std's Unix `Slice` Display: the whole lossy text (each
        // invalid sequence as U+FFFD) formats as a `str`, so width
        // and precision apply to all of it.
        let bytes = self.path.bytes();
        match crate::ffi::bytes_to_str(bytes) {
            Some(text) => f.pad(text),
            None => f.pad(&crate::ffi::bytes_to_string_lossy(bytes)),
        }
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", &self.inner)
    }
}

impl PathBuf {
    /// An empty `PathBuf`.
    pub fn new() -> PathBuf {
        PathBuf { inner: OsString::new() }
    }

    /// An empty `PathBuf` with room for `capacity` bytes.
    pub fn with_capacity(capacity: usize) -> PathBuf {
        PathBuf { inner: OsString::with_capacity(capacity) }
    }

    /// The `PathBuf` of an `OsString` (`From<OsString>`, for this crate:
    /// lust cannot call `PathBuf::from` yet).
    pub(crate) fn from_os_string(inner: OsString) -> PathBuf {
        PathBuf { inner }
    }

    /// The borrowed `Path`.
    pub fn as_path(&self) -> &Path {
        Path::new(&self.inner)
    }

    /// Extends the path with `path`: an absolute `path` replaces it,
    /// else a separator joins the two when needed.
    pub fn push<P: AsRef<Path>>(&mut self, path: P) {
        let path = path.as_ref();
        let bytes = self.inner.as_encoded_bytes();
        let need_sep = !bytes.is_empty() && bytes[bytes.len() - 1] != b'/';
        if path.is_absolute() {
            self.inner.clear();
        } else if need_sep {
            self.inner.push("/");
        }
        self.inner.push(path.as_os_str());
    }

    /// Truncates to the parent; false when there is no parent.
    pub fn pop(&mut self) -> bool {
        match self.as_path().parent() {
            Some(parent) => {
                let len = parent.as_os_str().len();
                self.inner.truncate(len);
                true
            }
            None => false,
        }
    }

    /// Replaces the file name (or adds one when there is none).
    pub fn set_file_name<S: AsRef<OsStr>>(&mut self, file_name: S) {
        if self.as_path().file_name().is_some() {
            self.pop();
        }
        self.push(Path::new(file_name.as_ref()));
    }

    /// Replaces the extension (an empty one removes it). False when the
    /// path has no file name. Panics when `extension` has a separator.
    pub fn set_extension<S: AsRef<OsStr>>(&mut self, extension: S) -> bool {
        let extension = extension.as_ref();
        for &b in extension.as_encoded_bytes() {
            if b == b'/' {
                panic!("extension cannot contain path separators: {:?}", extension); //@ std/src/path.rs:385:13
            }
        }
        let end = match self.file_stem_end() {
            None => return false,
            Some(end) => end,
        };
        self.inner.truncate(end);
        if !extension.is_empty() {
            self.inner.push(".");
            self.inner.push(extension);
        }
        true
    }

    /// The byte offset just past the file stem, None without a file name.
    fn file_stem_end(&self) -> Option<usize> {
        let mut comps = self.as_path().components();
        let (comp, at, len) = comps.next_back_range()?;
        let Component::Normal(name) = comp else { return None };
        let (before, after) = rsplit_file_at_dot(name);
        Some(match (before, after) {
            (Some(stem), _) => at + stem.len(),
            _ => at + len,
        })
    }

    /// The path as an `OsString`.
    pub fn into_os_string(self) -> OsString {
        self.inner
    }

    /// The buffer capacity in bytes.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Removes the contents, keeping the buffer.
    pub fn clear(&mut self) {
        self.inner.clear()
    }
}

impl Deref for PathBuf {
    type Target = Path;
    fn deref(&self) -> &Path {
        Path::new(&self.inner)
    }
}

impl Clone for PathBuf {
    fn clone(&self) -> PathBuf {
        PathBuf { inner: self.inner.clone() }
    }
}

impl ToOwned for Path {
    type Owned = PathBuf;

    fn to_owned(&self) -> PathBuf {
        PathBuf { inner: self.inner.to_os_string() }
    }

    fn clone_into(&self, target: &mut PathBuf) {
        self.inner.clone_into(&mut target.inner);
    }
}

impl Default for PathBuf {
    fn default() -> PathBuf {
        PathBuf::new()
    }
}

impl fmt::Debug for PathBuf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_path())
    }
}

impl AsRef<Path> for Path {
    fn as_ref(&self) -> &Path {
        self
    }
}

impl AsRef<Path> for PathBuf {
    fn as_ref(&self) -> &Path {
        self.as_path()
    }
}

impl AsRef<Path> for OsStr {
    fn as_ref(&self) -> &Path {
        Path::new(self)
    }
}

impl AsRef<Path> for OsString {
    fn as_ref(&self) -> &Path {
        Path::new(self)
    }
}

impl AsRef<Path> for str {
    fn as_ref(&self) -> &Path {
        Path::new(self)
    }
}

impl AsRef<Path> for String {
    fn as_ref(&self) -> &Path {
        Path::new(self)
    }
}

impl AsRef<OsStr> for Path {
    fn as_ref(&self) -> &OsStr {
        &self.inner
    }
}

impl AsRef<OsStr> for PathBuf {
    fn as_ref(&self) -> &OsStr {
        &self.inner
    }
}

impl From<String> for PathBuf {
    fn from(s: String) -> PathBuf {
        PathBuf { inner: OsString::__from_vec(s.into_bytes()) }
    }
}

impl From<OsString> for PathBuf {
    fn from(s: OsString) -> PathBuf {
        PathBuf { inner: s }
    }
}

impl From<&str> for PathBuf {
    fn from(s: &str) -> PathBuf {
        PathBuf { inner: OsString::__from_vec(core::intrinsics::sys_str_as_bytes(s).to_vec()) }
    }
}

impl From<&Path> for PathBuf {
    fn from(s: &Path) -> PathBuf {
        s.to_path_buf()
    }
}

impl From<&String> for PathBuf {
    fn from(s: &String) -> PathBuf {
        PathBuf { inner: OsString::__from_vec(core::intrinsics::sys_str_as_bytes(s).to_vec()) }
    }
}

impl From<PathBuf> for OsString {
    fn from(p: PathBuf) -> OsString {
        p.inner
    }
}

impl PartialEq for Path {
    fn eq(&self, other: &Path) -> bool {
        self.components() == other.components()
    }
}

impl Eq for Path {}

impl PartialOrd for Path {
    fn partial_cmp(&self, other: &Path) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Path {
    fn cmp(&self, other: &Path) -> Ordering {
        Ord::cmp(&self.components(), &other.components())
    }
}

// std's hash: the bytes of each component that `components()` keeps,
// then a word that mixes the component lengths, so ["foo", "bar"] and
// ["foobar"] differ. Skipping `.` after a separator matches `==`.
impl core::hash::Hash for Path {
    fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
        let bytes = self.bytes();
        let mut component_start = 0;
        let mut chunk_bits: usize = 0;
        for i in 0..bytes.len() {
            if bytes[i] == b'/' {
                if i > component_start {
                    let to_hash = &bytes[component_start..i];
                    chunk_bits = chunk_bits.wrapping_add(to_hash.len());
                    chunk_bits = chunk_bits.rotate_right(2);
                    h.write(to_hash);
                }
                component_start = i + 1;
                let tail = &bytes[component_start..];
                component_start += match tail {
                    [b'.'] => 1,
                    [b'.', b'/', ..] => 1,
                    _ => 0,
                };
            }
        }
        if component_start < bytes.len() {
            let to_hash = &bytes[component_start..];
            chunk_bits = chunk_bits.wrapping_add(to_hash.len());
            chunk_bits = chunk_bits.rotate_right(2);
            h.write(to_hash);
        }
        h.write_usize(chunk_bits);
    }
}

impl core::hash::Hash for PathBuf {
    fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
        self.as_path().hash(h)
    }
}

impl core::borrow::Borrow<Path> for PathBuf {
    fn borrow(&self) -> &Path {
        self.as_path()
    }
}

impl PartialEq for PathBuf {
    fn eq(&self, other: &PathBuf) -> bool {
        self.as_path() == other.as_path()
    }
}

impl Eq for PathBuf {}

impl PartialOrd for PathBuf {
    fn partial_cmp(&self, other: &PathBuf) -> Option<Ordering> {
        Some(self.as_path().cmp(other.as_path()))
    }
}

impl Ord for PathBuf {
    fn cmp(&self, other: &PathBuf) -> Ordering {
        self.as_path().cmp(other.as_path())
    }
}

// Cross-type comparisons, all through components as in std.
impl PartialEq<PathBuf> for Path {
    fn eq(&self, other: &PathBuf) -> bool {
        self == other.as_path()
    }
}

impl PartialEq<Path> for PathBuf {
    fn eq(&self, other: &Path) -> bool {
        self.as_path() == other
    }
}

impl PartialEq<PathBuf> for &Path {
    fn eq(&self, other: &PathBuf) -> bool {
        *self == other.as_path()
    }
}

impl PartialEq<&Path> for PathBuf {
    fn eq(&self, other: &&Path) -> bool {
        self.as_path() == *other
    }
}

impl PartialEq<str> for Path {
    fn eq(&self, other: &str) -> bool {
        self == Path::new(other)
    }
}

impl PartialEq<Path> for str {
    fn eq(&self, other: &Path) -> bool {
        Path::new(self) == other
    }
}

impl PartialEq<String> for Path {
    fn eq(&self, other: &String) -> bool {
        self == Path::new(other)
    }
}

impl PartialEq<Path> for String {
    fn eq(&self, other: &Path) -> bool {
        Path::new(self) == other
    }
}

impl PartialEq<str> for PathBuf {
    fn eq(&self, other: &str) -> bool {
        self.as_path() == Path::new(other)
    }
}

impl PartialEq<PathBuf> for str {
    fn eq(&self, other: &PathBuf) -> bool {
        Path::new(self) == other.as_path()
    }
}

impl PartialEq<String> for PathBuf {
    fn eq(&self, other: &String) -> bool {
        self.as_path() == Path::new(other)
    }
}

impl PartialEq<PathBuf> for String {
    fn eq(&self, other: &PathBuf) -> bool {
        Path::new(self) == other.as_path()
    }
}

impl PartialEq<OsStr> for Path {
    fn eq(&self, other: &OsStr) -> bool {
        self == Path::new(other)
    }
}

impl PartialEq<OsString> for Path {
    fn eq(&self, other: &OsString) -> bool {
        self == Path::new(other)
    }
}

impl PartialEq<OsString> for &Path {
    fn eq(&self, other: &OsString) -> bool {
        *self == Path::new(other)
    }
}

impl PartialEq<&OsStr> for Path {
    fn eq(&self, other: &&OsStr) -> bool {
        self == Path::new(*other)
    }
}

impl PartialEq<OsStr> for PathBuf {
    fn eq(&self, other: &OsStr) -> bool {
        self.as_path() == Path::new(other)
    }
}

impl PartialEq<OsString> for PathBuf {
    fn eq(&self, other: &OsString) -> bool {
        self.as_path() == Path::new(other)
    }
}

impl PartialEq<&OsStr> for PathBuf {
    fn eq(&self, other: &&OsStr) -> bool {
        self.as_path() == Path::new(*other)
    }
}

impl PartialEq<Path> for OsStr {
    fn eq(&self, other: &Path) -> bool {
        Path::new(self) == other
    }
}

impl PartialEq<PathBuf> for OsStr {
    fn eq(&self, other: &PathBuf) -> bool {
        Path::new(self) == other.as_path()
    }
}

impl PartialEq<Path> for OsString {
    fn eq(&self, other: &Path) -> bool {
        Path::new(self) == other
    }
}

impl PartialEq<PathBuf> for OsString {
    fn eq(&self, other: &PathBuf) -> bool {
        Path::new(self) == other.as_path()
    }
}

impl PartialOrd<PathBuf> for Path {
    fn partial_cmp(&self, other: &PathBuf) -> Option<Ordering> {
        Some(self.cmp(other.as_path()))
    }
}

impl PartialOrd<Path> for PathBuf {
    fn partial_cmp(&self, other: &Path) -> Option<Ordering> {
        Some(self.as_path().cmp(other))
    }
}
