use core::fmt::{Debug, Display, Formatter};

pub enum TinyLFUError {
    InvalidCountMinWidth(u64),
    InvalidSamples(usize),
    InvalidWindowCacheSize(usize),
    InvalidProbationaryCacheSize(usize),
    InvalidProtectedCacheSize(usize),
    InvalidFalsePositiveRatio(f64),
}

impl TinyLFUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            TinyLFUError::InvalidSamples(v) => write!(f, "invalid number of samples: {}", *v),
            TinyLFUError::InvalidCountMinWidth(v) => {
                write!(f, "invalid count main sketch width: {}", *v)
            }
            TinyLFUError::InvalidWindowCacheSize(v) => {
                write!(f, "invalid window cache size: {}", *v)
            }
            TinyLFUError::InvalidProbationaryCacheSize(v) => {
                write!(f, "invalid probationary cache size: {}", *v)
            }
            TinyLFUError::InvalidProtectedCacheSize(v) => {
                write!(f, "invalid protected cache size: {}", *v)
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
