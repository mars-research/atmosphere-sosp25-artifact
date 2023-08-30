//! I/O utilities.

use core::convert::AsRef;

use displaydoc::Display;
use embedded_io as eio;
pub use embedded_io::{
    Read, Seek, SeekFrom, Write,
    ReadExactError, WriteAllError, WriteFmtError,
    ErrorType, ErrorKind,
};

/// An I/O error.
#[derive(Debug, Display)]
pub struct Error {
    kind: ErrorKind,
}

/// Wrapper of an in-memory buffer tha implements `Read` and `Seek`.
///
/// This is the no-std version of `std::io::Cursor`.
///
/// The implementation is copied from `rust/library/std/src/io/cursor.rs`.
pub struct Cursor<T> {
    inner: T,
    pos: u64,
}

impl Error {
    /// Returns a new Error.
    pub fn from_kind(kind: eio::ErrorKind) -> Self {
        Self { kind }
    }
}

impl eio::Error for Error {
    fn kind(&self) -> eio::ErrorKind {
        eio::ErrorKind::Other
    }
}

impl<T> Cursor<T> {
    /// Creates a new Cursor.
    pub fn new(inner: T) -> Self {
        Self { inner, pos: 0 }
    }
}

impl<T> Cursor<T>
where
    T: AsRef<[u8]>,
{
    /// Returns the remaining slice.
    pub fn remaining_slice(&self) -> &[u8] {
        let len = self.pos.min(self.inner.as_ref().len() as u64);
        &self.inner.as_ref()[(len as usize)..]
    }
}

impl<T> Read for Cursor<T>
where
    T: AsRef<[u8]>,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let n = Read::read(&mut self.remaining_slice(), buf).unwrap();
        self.pos += n as u64;
        Ok(n)
    }
}

impl<T> Seek for Cursor<T>
where
    T: AsRef<[u8]>,
{
    fn seek(&mut self, style: SeekFrom) -> Result<u64, Self::Error> {
        let (base_pos, offset) = match style {
            SeekFrom::Start(n) => {
                self.pos = n;
                return Ok(n);
            }
            SeekFrom::End(n) => (self.inner.as_ref().len() as u64, n),
            SeekFrom::Current(n) => (self.pos, n),
        };
        match base_pos.checked_add_signed(offset) {
            Some(n) => {
                self.pos = n;
                Ok(self.pos)
            }
            None => Err(Error {
                kind: eio::ErrorKind::InvalidInput,
            }),
        }
    }
}

impl<T> eio::ErrorType for Cursor<T> {
    type Error = Error;
}
