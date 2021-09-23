#[cfg(feature = "std")]
mod impl_std;
#[cfg(not(feature = "std"))]
mod impl_core;

use crate::lfu::error::LFUError;

const DEPTH: usize = 4;

// return the integer >= i which is a power of two
fn next_power_of_2(num: u64) -> u64 {
    let mut num = num - 1;
    num |= num >> 1;
    num |= num >> 2;
    num |= num >> 4;
    num |= num >> 8;
    num |= num >> 16;
    num += 1;
    num
}