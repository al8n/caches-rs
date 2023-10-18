//! This mod implements a Simple Bloom Filter.
//!
//! This file is a mechanical translation of the reference Golang code, available at [here](https://github.com/dgraph-io/ristretto/blob/master/z/bbloom.go)
//!
//! I claim no additional copyright over the original implementation.
use alloc::vec;
use alloc::vec::Vec;

const LN_2: f64 = core::f64::consts::LN_2;

const MASK: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];

/// Bloom filter
pub(crate) struct Bloom {
    bitset: Vec<u64>,
    elem_num: u64,
    size: u64,
    set_locs: u64,
    shift: u64,
}

impl Bloom {
    /// Create a new Bloom filter
    pub fn new(entries: usize, wrongs_or_locs: f64) -> Self {
        let (entries, locs) = if wrongs_or_locs < 1.0 {
            Bloom::calc_size_by_wrong_positives(entries, wrongs_or_locs)
        } else {
            (entries as u64, wrongs_or_locs as u64)
        };

        let (size, exponent) = Bloom::get_size(entries);

        let mut bloom = Bloom {
            bitset: Vec::new(),
            elem_num: 0,
            size: size - 1,
            set_locs: locs,
            shift: 64 - exponent,
        };
        bloom.set_size(size);
        bloom
    }

    fn calc_size_by_wrong_positives(num_entries: usize, wrongs: f64) -> (u64, u64) {
        let size = -1.0 * (num_entries as f64) * wrongs.ln() / LN_2.powi(2);
        let locs = (LN_2 * size / (num_entries as f64)).ceil();
        (size as u64, locs as u64)
    }

    fn get_size(ui64: u64) -> (u64, u64) {
        let mut size = 1;
        let mut exponent = 0;
        while size < ui64 {
            size <<= 1;
            exponent += 1;
        }
        (size, exponent)
    }

    /// `add` adds hash of a key to the bloom filter
    pub fn add(&mut self, hash: u64) {
        let h = hash >> self.shift;
        let l = hash << self.shift >> self.shift;
        for i in 0..self.set_locs {
            self.set((h + i * l) & self.size);
            self.elem_num += 1;
        }
    }

    /// `contains` checks if bit(s) for entry hash is/are set,
    /// returns true if the hash was added to the Bloom Filter.
    pub fn contains(&self, hash: u64) -> bool {
        let h = hash >> self.shift;
        let l = hash << self.shift >> self.shift;
        for i in 0..self.set_locs {
            if !self.is_set((h + i * l) & self.size) {
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

    // pub fn total_size(&self) -> usize {
    //     self.bitset.len() * 8 + 5 * 8
    // }

    fn set_size(&mut self, sz: u64) {
        self.bitset = vec![0; (sz >> 6) as usize];
    }

    /// `clear` clear the `Bloom` filter
    pub fn clear(&mut self) {
        for i in &mut self.bitset {
            *i = 0;
        }
    }

    /// `set` sets the bit[idx] of bitset
    pub fn set(&mut self, idx: u64) {
        let idx = idx as usize;
        self.bitset[idx >> 6] |= MASK[idx % 8] as u64;
    }

    /// `is_set` checks if bit[idx] of bitset is set, returns true/false.
    pub fn is_set(&self, idx: u64) -> bool {
        let idx = idx as usize;
        (self.bitset[idx >> 6] & MASK[idx % 8] as u64) != 0
    }
}

#[cfg(test)]
mod test {
    use crate::lfu::tinylfu::bloom::Bloom;
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::hash::{Hash, Hasher};
    use rand::distributions::Alphanumeric;
    use rand::{thread_rng, Rng};
    use std::collections::hash_map::DefaultHasher;
    use std::println;

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

        println!("Bloomfilter(size = {}) Check for 'false positives': {} wrong positive 'Has' results on 2^16 entries => {}%", bf.bitset.len() << 6, cnt, cnt as f64 / N as f64);
    }
}
