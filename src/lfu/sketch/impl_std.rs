use crate::lfu::sketch::{next_power_of_2, DEPTH};
use crate::lfu::error::LFUError;
use std::time::Instant;
use std::vec::Vec;
use std::vec;
use rand::{RngCore, Error, thread_rng, rngs::{
    ThreadRng, StdRng
}, SeedableRng, Rng};
use core::time::Duration;
use chrono::{Utc, TimeZone};


/// `CountMinSketch` is a small conservative-update count-min sketch
/// implementation with 4-bit counters
struct CountMinSketch<const T: usize> {
    rows: [Vec<u8>; T],
    seeds: [u64; T],
    mask: u64,
}

impl CountMinSketch<DEPTH> {
    pub(crate) fn new(ctrs: u64) -> Result<Self, LFUError> {
        if ctrs < 1 {
            return Err(LFUError::BadWidth(ctrs));
        }

        let ctrs = next_power_of_2(ctrs);
        let hctrs = (ctrs / 2) as usize;

        let mut source = StdRng::seed_from_u64(Utc::now().timestamp_nanos().unsigned_abs());

        let seeds: Vec<u64> = {
            (0..DEPTH).map(|_| {
                source.gen::<u64>()
            }).collect()
        };

        let this  = Self {
            rows: [vec![0; hctrs], vec![0; hctrs], vec![0; hctrs], vec![0; hctrs]],
            seeds: [seeds[0], seeds[1], seeds[2], seeds[3]],
            mask: ctrs - 1,
        };

        Ok(this)
    }

    pub(crate) fn add(&mut self, key: u64) {

    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_shift() {
        assert_eq!(16 >> 2, 4);
    }
}