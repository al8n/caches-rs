//! This mod implements Count-Min sketch with 4-bit counters.
//!
//! This file is a mechanical translation of the reference Golang code, available at https://github.com/dgraph-io/ristretto/blob/master/sketch.go
//!
//! I claim no additional copyright over the original implementation.
use crate::lfu::tinylfu::sketch::{next_power_of_2, DEPTH, CountMinRow};
use alloc::vec::Vec;
use rand::{rngs::StdRng, SeedableRng, Rng};
use chrono::{Utc};
use crate::lfu::tinylfu::error::TinyLFUError;


/// `CountMinSketch` is a small conservative-update count-min sketch
/// implementation with 4-bit counters
pub(crate) struct CountMinSketch {
    rows: [CountMinRow; DEPTH],
    seeds: [u64; DEPTH],
    mask: u64,
}

impl CountMinSketch {
    pub(crate) fn new(ctrs: u64) -> Result<Self, TinyLFUError> {
        if ctrs < 1 {
            return Err(TinyLFUError::InvalidCountMinWidth(ctrs));
        }

        let ctrs = next_power_of_2(ctrs);
        let hctrs = ctrs / 2;

        let mut source = StdRng::seed_from_u64(Utc::now().timestamp_nanos().unsigned_abs());

        let seeds: Vec<u64> = {
            (0..DEPTH).map(|_| {
                source.gen::<u64>()
            }).collect()
        };

        let this  = Self {
            rows: [CountMinRow::new(hctrs), CountMinRow::new(hctrs), CountMinRow::new(hctrs), CountMinRow::new(hctrs)],
            seeds: [seeds[0], seeds[1], seeds[2], seeds[3]],
            mask: ctrs - 1,
        };

        Ok(this)
    }

    /// `increment` increments the count(ers) for the specified key.
    pub(crate) fn increment(&mut self, hashed: u64) {
        let mask = self.mask;
        (0..DEPTH).for_each(|i| {
            let seed = self.seeds[i];
            self.rows[i].increment((hashed ^ seed) & mask);
        })
    }

    /// `estimate` returns the value of the specified key.
    pub(crate) fn estimate(&self, hashed: u64) -> u64 {
        let mask = self.mask;
        let mut min = 255u8;
        (0..DEPTH).for_each(|i| {
            let seed = self.seeds[i];
            let val = self.rows[i].get((hashed ^ seed) & mask);
            if val < min {
                min = val;
            }
        });

        min as u64
    }

    /// `reset` halves all counter values.
    pub(crate) fn reset(&mut self) {
        self.rows.iter_mut().for_each(|row| row.reset())
    }

    /// `clear` zeroes all counters.
    pub(crate) fn clear(&mut self) {
        self.rows.iter_mut().for_each(|row| row.clear())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::format;

    #[test]
    fn test_count_min_sketch() {
        let s = CountMinSketch::new(5).unwrap();
        assert_eq!(7u64, s.mask);
    }

    #[test]
    fn test_count_min_sketch_increment() {
        let mut s = CountMinSketch::new(16).unwrap();
        s.increment(1);
        s.increment(5);
        s.increment(9);
        for i in 0..DEPTH {
            if format!("{:?}", s.rows[i]) != format!("{:?}", s.rows[0]) {
                break;
            }
            assert_ne!(i, DEPTH - 1);
        }
    }

    #[test]
    fn test_count_min_sketch_estimate() {
        let mut s = CountMinSketch::new(16).unwrap();
        s.increment(1);
        s.increment(1);

        assert_eq!(s.estimate(1), 2);
        assert_eq!(s.estimate(0), 0);
    }

    #[test]
    fn test_count_min_sketch_reset() {
        let mut s = CountMinSketch::new(16).unwrap();
        s.increment(1);
        s.increment(1);
        s.increment(1);
        s.increment(1);
        s.reset();
        assert_eq!(s.estimate(1), 2);
    }

    #[test]
    fn test_count_min_sketch_clear() {
        let mut s = CountMinSketch::new(16).unwrap();
        (0..16).for_each(|i| s.increment(i));
        s.clear();
        (0..16).for_each(|i| assert_eq!(s.estimate(i), 0));
    }
}