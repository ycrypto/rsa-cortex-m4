/// There is but one – failure 🤪.
#[derive(Debug)]
pub struct Error;

/// [`Error`] or success.
pub type Result<T> = core::result::Result<T, Error>;
