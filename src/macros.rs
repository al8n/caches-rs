#[macro_export]
#[doc(hidden)]
macro_rules! import_hashbrown {
    ($($t:ident),*) => {
        #[cfg(feature = "hashbrown")]
        use hashbrown::{$($t),*,};
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! import_std {
    ($($t:ident),*) => {
        #[cfg(not(feature = "hashbrown"))]
        use std::collections::{$($t),*,};
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! cfg_not_nightly {
    ($($item:item)*) => {
        $(
            #[cfg(not(feature = "nightly"))]
            #[cfg_attr(docsrs, doc(cfg(not(feature = "nightly"))))]
            $item
        )*
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! cfg_nightly {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "nightly")]
            #[cfg_attr(docsrs, doc(cfg(feature = "nightly")))]
            $item
        )*
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! cfg_nightly_hidden_doc {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "nightly")]
            #[doc(hidden)]
            $item
        )*
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! cfg_std {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "std")]
            #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
            $item
        )*
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! cfg_not_std {
    ($($item:item)*) => {
        $(
            #[cfg(not(feature = "std"))]
            #[cfg_attr(docsrs, doc(cfg(not(feature = "std"))))]
            $item
        )*
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! cfg_hashbrown {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "hashbrown")]
            #[cfg_attr(docsrs, doc(cfg(feature = "hashbrown")))]
            $item
        )*
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! cfg_not_hashbrown {
    ($($item:item)*) => {
        $(
            #[cfg(not(feature = "hashbrown"))]
            #[cfg_attr(docsrs, doc(cfg(not(feature = "hashbrown"))))]
            $item
        )*
    }
}
