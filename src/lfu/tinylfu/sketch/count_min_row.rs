//! This mod implements Count Min Row.
//!
//! This file is a mechanical translation of the reference Golang code, available at https://github.com/dgryski/go-tinylfu/blob/master/cm4.go
//!
//! I claim no additional copyright over the original implementation.
use alloc::fmt::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::{Debug, Formatter};
use core::ops::{Index, IndexMut};

pub(crate) struct CountMinRow(Vec<u8>);

impl CountMinRow {
    pub(crate) fn new(width: u64) -> Self {
        Self(vec![0; width as usize])
    }

    pub(crate) fn get(&self, i: u64) -> u8 {
        ((self[(i / 2) as usize] >> ((i & 1) * 4)) as u8) & 0x0f
    }

    pub(crate) fn increment(&mut self, i: u64) {
        // Index of the counter
        let idx = (i / 2) as usize;
        // shift distance (even 0, odd 4).
        let shift = (i & 1) * 4;
        // counter value
        let v = (self[idx] >> shift) & 0x0f;
        // only increment if not max value (overflow wrap is bad for LFU).
        if v < 15 {
            self[idx] += 1 << shift;
        }
    }

    pub(crate) fn reset(&mut self) {
        // halve each counter
        self.0.iter_mut().for_each(|v| *v = (*v >> 1) & 0x77)
    }

    pub(crate) fn clear(&mut self) {
        // zero each counter
        self.0.iter_mut().for_each(|v| *v = 0)
    }
}

impl Index<usize> for CountMinRow {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
    }
}

impl IndexMut<usize> for CountMinRow {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.0.index_mut(index)
    }
}

impl Debug for CountMinRow {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let mut s = String::new();
        for i in 0..(self.0.len() * 2) {
            s.push_str(&format(format_args!(
                "{:02} ",
                (self[i / 2] >> ((i & 1) * 4)) & 0x0f
            )));
        }
        write!(f, "{}", s)
    }
}

#[cfg(test)]
mod test {
    use crate::lfu::tinylfu::sketch::count_min_row::CountMinRow;

    #[test]
    fn test_count_min_row() {
        let mut cmr = CountMinRow::new(8);
        cmr.increment(0);
        assert_eq!(cmr[0], 0x01);

        assert_eq!(cmr.get(0), 1);
        assert_eq!(cmr.get(1), 0);

        cmr.increment(1);
        assert_eq!(cmr[0], 0x11);
        assert_eq!(cmr.get(0), 1);
        assert_eq!(cmr.get(1), 1);

        (0..14).for_each(|_| cmr.increment(1));
        assert_eq!(cmr[0], 0xf1);
        assert_eq!(cmr.get(1), 15);
        assert_eq!(cmr.get(0), 1);

        // ensure clamped
        (0..3).for_each(|_| {
            cmr.increment(1);
            assert_eq!(cmr[0], 0xf1);
        });

        cmr.reset();
        assert_eq!(cmr[0], 0x70);
    }
}
