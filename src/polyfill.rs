/// Three level poliyfill dor the f64 `ceil`, `ln`, and `floor` functions.
/// Using these functions in a no_std context falls back to libm's manual
/// implementation from musl's libc.
/// Using the nightly feature allows the upgrade to using LLVM hints, and
/// allowing LLVM to provide a software fallback for target platforms
/// witout hardware f64 instructions.

cfg_if! {
    if #[cfg(feature = "std")] {
        #[inline(always)]
        pub(crate) fn ceil(val: f64) -> f64 {
            val.ceil()
        }
        #[inline(always)]
        pub(crate) fn ln(val: f64) -> f64 {
            val.ln()
        }
        #[inline(always)]
        pub(crate) fn floor(val: f64) -> f64 {
            val.floor()
        }
    } else {
        use libm;
        #[inline(always)]
        pub(crate) fn ceil(val: f64) -> f64 {
            libm::ceil(val)
        }
        #[inline(always)]
        pub(crate) fn ln(val: f64) -> f64 {
            libm::log(val)
        }
        #[inline(always)]
        pub(crate) fn floor(val: f64) -> f64 {
            libm::floor(val)
        }
    }
}
