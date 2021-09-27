use core::fmt::{Debug, Display, Formatter};

pub enum WTinyLFUError {
    InvalidCountMinWidth(u64),
    InvalidSamples(usize),
    InvalidWindowCacheSize(usize),
    InvalidProbationaryCacheSize(usize),
    InvalidProtectedCacheSize(usize),
    InvalidFalsePositiveRatio(f64),
    Unknown,
}

impl WTinyLFUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            WTinyLFUError::InvalidSamples(v) => write!(f, "invalid number of samples: {}", *v),
            WTinyLFUError::InvalidCountMinWidth(v) => {
                write!(f, "invalid count main sketch width: {}", *v)
            }
            WTinyLFUError::InvalidWindowCacheSize(v) => {
                write!(f, "invalid window cache size: {}", *v)
            }
            WTinyLFUError::InvalidProbationaryCacheSize(v) => {
                write!(f, "invalid probationary cache size: {}", *v)
            }
            WTinyLFUError::InvalidProtectedCacheSize(v) => {
                write!(f, "invalid protected cache size: {}", *v)
            }
            WTinyLFUError::InvalidFalsePositiveRatio(v) => write!(
                f,
                "invalid false positive ratio: {}, which should be in range (0.0, 1.0)",
                *v
            ),
            WTinyLFUError::Unknown => write!(f, "Unknown error"),
        }
    }
}

impl Display for WTinyLFUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.fmt(f)
    }
}

impl Debug for WTinyLFUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.fmt(f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for WTinyLFUError {}
