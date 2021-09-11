#[macro_export]
macro_rules! import_hash {
    ($($t:ty),*) => {
        #[cfg(feature = "hashbrown")]
        use hashbrown::{$($t,)*};
        #[cfg(not(feature = "hashbrown"))]
        use std::collections::{$($t,)*};
    }
}
