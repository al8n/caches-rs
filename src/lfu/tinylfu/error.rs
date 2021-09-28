use core::fmt::{Debug, Display, Formatter};

/// TinyLFUError contains the error of TinyLFU
pub enum TinyLFUError {
    /// Count Min sketch with wrong width
    InvalidCountMinWidth(u64),
    /// Invalid Samples value for TinyLFU
    InvalidSamples(usize),
    /// Invalid false positive ratio for TinyLFU
    InvalidFalsePositiveRatio(f64),
}

impl TinyLFUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            TinyLFUError::InvalidSamples(v) => write!(f, "invalid number of samples: {}", *v),
            TinyLFUError::InvalidCountMinWidth(v) => {
                write!(f, "invalid count main sketch width: {}", *v)
            }
            TinyLFUError::InvalidFalsePositiveRatio(v) => write!(
                f,
                "invalid false positive ratio: {}, which should be in range (0.0, 1.0)",
                *v
            ),
        }
    }
}

impl Display for TinyLFUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.fmt(f)
    }
}

impl Debug for TinyLFUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.fmt(f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TinyLFUError {}
