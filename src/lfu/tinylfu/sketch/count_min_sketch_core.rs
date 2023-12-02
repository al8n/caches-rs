//! This mod implements Count-Min sketch with 4-bit counters.
//!
//! This file is a mechanical translation of the reference Golang code, available at [here](https://github.com/dgryski/go-tinylfu/blob/master/cm4.go)
//!
//! I claim no additional copyright over the original implementation.
use crate::lfu::tinylfu::error::TinyLFUError;
use crate::lfu::tinylfu::sketch::{next_power_of_2, CountMinRow, DEPTH};

#[cfg(feature = "std")]
use alloc::vec::{self, Vec};
#[cfg(feature = "std")]
use core::ops::{Index, IndexMut};

/// `CountMinSketch` is a small conservative-update count-min sketch
/// implementation with 4-bit counters
#[derive(Clone)]
pub(crate) struct CountMinSketch {
    rows: [CountMinRow; DEPTH],
    mask: u64,
}

impl CountMinSketch {
    pub(crate) fn new(ctrs: u64) -> Result<Self, TinyLFUError> {
        if ctrs < 1 {
            return Err(TinyLFUError::InvalidCountMinWidth(ctrs));
        }

        let ctrs = next_power_of_2(ctrs);
        let hctrs = ctrs / 2;

        let this = Self {
            rows: [
                CountMinRow::new(hctrs),
                CountMinRow::new(hctrs),
                CountMinRow::new(hctrs),
                CountMinRow::new(hctrs),
            ],
            mask: ctrs - 1,
        };

        Ok(this)
    }

    pub(crate) fn increment(&mut self, key_hash: u64) {
        let h = key_hash;
        let l = key_hash >> 32;
        let mask = self.mask;
        self.rows.iter_mut().enumerate().for_each(|(idx, row)| {
            let idx = idx as u64;
            let pos = (h + idx * l) & mask;
            row.increment(pos);
        });
    }

    pub(crate) fn estimate(&self, key_hash: u64) -> u64 {
        let h = key_hash;
        let l = key_hash >> 32;

        let mut min = 255u8;
        (0..DEPTH).for_each(|i| {
            let idx = i as u64;
            let pos = (h + idx * l) & self.mask;
            let v = self.rows[i].get(pos);
            if v < min {
                min = v;
            }
        });
        min.into()
    }

    pub(crate) fn reset(&mut self) {
        self.rows.iter_mut().for_each(|row| row.reset())
    }

    pub(crate) fn clear(&mut self) {
        self.rows.iter_mut().for_each(|row| row.clear())
    }
}

#[cfg(test)]
mod test {
    use crate::lfu::tinylfu::sketch::CountMinSketch;

    #[test]
    fn test_count_min_sketch() {
        let mut cm = CountMinSketch::new(32).unwrap();
        let hash: u64 = 0x0ddc0ffeebadf00d;
        cm.increment(hash);
        cm.increment(hash);

        assert_eq!(cm.estimate(hash), 2);
    }
}
