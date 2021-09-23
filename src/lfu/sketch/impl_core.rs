use crate::lfu::sketch::{DEPTH, next_power_of_2};
use crate::lfu::error::LFUError;

use alloc::vec::Vec;



/// `CountMinSketch` is a small conservative-update count-min sketch
/// implementation with 4-bit counters
pub(crate) struct CountMinSketch<const T: usize> {
    rows: [Vec<u8>; T],
    mask: u64,
}

impl CountMinSketch<DEPTH> {
    pub(crate) fn new() -> Result<Self, LFUError> {
        if ctrs < 1 {
            return Err(LFUError::BadWidth(ctrs));
        }

        let ctrs = next_power_of_2(ctrs);
        let hctrs = (ctrs / 2) as usize;

        let this  = Self {
            rows: [vec![0; hctrs], vec![0; hctrs], vec![0; hctrs], vec![0; hctrs]],
            mask: ctrs - 1,
        };

        Ok(this)
    }

    pub(crate) fn add(&mut self, key_hash: u64) {
        let h = key_hash;
        let l = key_hash >> 32;


    }

    fn increase(&mut self, i: u64) {
        let idx = i >> 1;
        let shift = (i & 1) << 2;
    }
}