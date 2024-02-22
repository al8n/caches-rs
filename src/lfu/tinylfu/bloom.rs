//! This mod implements a Simple Bloom Filter.
//!
//! This file is a mechanical translation of the reference Golang code, available at <https://github.com/dgraph-io/ristretto/blob/master/z/bbloom.go>
//!
//! I claim no additional copyright over the original implementation.

// use bitvec::vec::BitVec;
use alloc::{vec, vec::Vec};

use crate::polyfill::{ceil, ln};

const LN_2: f64 = core::f64::consts::LN_2;
const LN_2_2: f64 = LN_2 * LN_2;

fn get_size(ui64: u64) -> (u64, u64) {
    let ui64 = if ui64 < 512 { 512 } else { ui64 };
    let mut size = 1;
    let mut exponent = 0;
    while size < ui64 {
        size <<= 1;
        exponent += 1;
    }
    (size, exponent)
}

fn calc_size_by_wrong_positives(num_entries: f64, wrongs: f64) -> (u64, u64) {
    let size = ceil(-num_entries * ln(wrongs) / LN_2_2) as u64;
    let locs = ceil(LN_2 * size as f64 / num_entries) as u64;
    (size, locs)
}

/// Bloom filter
#[derive(Clone)]
#[repr(C)]
pub(crate) struct Bloom {
    bitset: Vec<u64>,
    elem_num: u64,
    size_exp: u64,
    size: u64,
    set_locs: u64,
    shift: u64,
}

impl Bloom {
    pub fn new(entries: usize, locs_or_err: f64) -> Self {
        let (entries, locs) = if locs_or_err < 1.0 {
            calc_size_by_wrong_positives(entries as f64, locs_or_err)
        } else {
            (entries as u64, locs_or_err as u64)
        };

        let (size, exponent) = get_size(entries);
        Bloom {
            bitset: vec![0; size as usize >> 6],
            elem_num: 0,
            size_exp: exponent,
            size: size - 1,
            set_locs: locs,
            shift: 64 - exponent,
        }
    }

    /// `size` makes Bloom filter with as bitset of size sz.
    #[inline]
    #[allow(dead_code)]
    pub fn size(&mut self, sz: usize) {
        self.bitset.resize(sz >> 6, 0)
    }

    /// Returns the exp of the size
    #[inline]
    #[allow(dead_code)]
    pub fn size_exp(&self) -> u64 {
        self.size_exp
    }

    /// `clear` clear the `Bloom` filter
    pub fn clear(&mut self) {
        self.bitset.fill(0)
    }

    /// `set` sets the bit[idx] of bitset
    pub fn set(&mut self, idx: u64) {
        let array_index = (idx >> 6) as usize;
        let bit_index = idx % 64;
        self.bitset[array_index] |= 1 << bit_index;
    }

    /// `is_set` checks if bit[idx] of bitset is set, returns true/false.
    pub fn is_set(&self, idx: u64) -> bool {
        let array_index = (idx >> 6) as usize;
        let bit_index = idx % 64;
        (self.bitset[array_index] & (1 << bit_index)) != 0
    }

    /// `add` adds hash of a key to the bloom filter
    pub fn add(&mut self, hash: u64) {
        let h = hash >> self.shift;
        let l = (hash << self.shift) >> self.shift;
        for i in 0..self.set_locs {
            let index = (h + i * l) & self.size;
            self.set(index);
            self.elem_num += 1;
        }
    }

    /// `contains` checks if bit(s) for entry hash is/are set,
    /// returns true if the hash was added to the Bloom Filter.
    pub fn contains(&self, hash: u64) -> bool {
        let h = hash >> self.shift;
        let l = (hash << self.shift) >> self.shift;
        for i in 0..self.set_locs {
            let index = (h + i * l) & self.size;
            if !self.is_set(index) {
                return false;
            }
        }
        true
    }

    /// `contains_or_add` only Adds hash, if it's not present in the bloomfilter.
    /// Returns true if hash was added.
    /// Returns false if hash was already registered in the bloomfilter.
    pub fn contains_or_add(&mut self, hash: u64) -> bool {
        if self.contains(hash) {
            false
        } else {
            self.add(hash);
            true
        }
    }

    /// `total_size` returns the total size of the bloom filter.
    #[allow(dead_code)]
    #[inline]
    pub fn total_size(&self) -> usize {
        // The bl struct has 5 members and each one is 8 byte. The bitset is a
        // uint64 byte slice.
        self.bitset.len() * 8 + 5 * 8
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::vec::Vec;
    use rand::distributions::Alphanumeric;
    use rand::{thread_rng, Rng};
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use std::string::String;

    const N: usize = 1 << 16;

    fn get_word_list() -> Vec<Vec<u8>> {
        let mut word_list = Vec::<Vec<u8>>::with_capacity(N);
        (0..N).for_each(|_| {
            let rand_string: String = thread_rng()
                .sample_iter(&Alphanumeric)
                .take(30)
                .map(char::from)
                .collect();
            word_list.push(rand_string.as_bytes().to_vec());
        });
        word_list
    }

    fn calculate_hash<T: Hash>(t: &T) -> u64 {
        let mut s = DefaultHasher::new();
        t.hash(&mut s);
        s.finish()
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_number_of_wrongs() {
        let mut bf = Bloom::new(N * 10, 7f64);

        let mut cnt = 0;
        get_word_list().into_iter().for_each(|words| {
            let hash = calculate_hash(&words);
            if !bf.contains_or_add(hash) {
                cnt += 1;
            }
        });

        std::println!("Bloomfilter(size = {}) Check for 'false positives': {} wrong positive 'Has' results on 2^16 entries => {}%", bf.bitset.len() << 6, cnt, cnt as f64 / N as f64);
    }

    #[test]
    fn test_total_size() {
        let bf = Bloom::new(10, 7f64);
        assert_eq!(bf.total_size(), 104);
    }

    #[test]
    fn test_size_exp() {
        let bf = Bloom::new(10, 7f64);
        assert_eq!(bf.size_exp(), 9);
    }

    #[test]
    fn test_size() {
        let mut bf = Bloom::new(10, 7f64);
        bf.size(1024);
        assert_eq!(bf.bitset.len(), 16);
    }
}
