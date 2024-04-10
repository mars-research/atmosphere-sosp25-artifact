//! Common memory utilities.

/// Protection on a page.
#[derive(Debug, Clone, Copy)]
pub struct PageProtection {
    /// The page can be read.
    pub read: bool,

    /// The page can be written.
    pub write: bool,

    /// The page can be executed.
    pub execute: bool,
}
