
use core::ptr::{addr_of};
use alloc::vec::Vec;
use alloc::vec;

const MASK: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];

const LN_2: f64 = 0.69314718056;

struct Size {
    size: u64,
    exp: u64,
}

fn get_size(n: u64) -> Size {
    let mut n = n;
    if n < 512 {
        n = 512;
    }

    let mut size = 1u64;
    let mut exp = 0u64;
    while size < n {
        size <<= 1;
        exp += 1;
    }

    Size {
        size,
        exp
    }
}

struct EntriesLocs {
    entries: u64,
    locs: u64,
}

fn calc_size_by_wrong_positives(num_entries: f64, wrongs: f64) -> EntriesLocs {
    let size = -1f64 * num_entries * wrongs.ln() / LN_2.powf(2f64);
    let locs = (LN_2 * size / num_entries).ceil();

    EntriesLocs {
        entries: size as u64,
        locs: locs as u64
    }
}

/// Bloom filter
pub struct Bloom {
    bitset: Vec<u64>,
    elem_num: u64,
    size_exp: u64,
    size: u64,
    set_locs: u64,
    shift: u64
}

pub enum RistrettoError {
    InvalidParams
}

impl Bloom {
    pub fn new(params: Vec<f64>) -> Result<Self, RistrettoError> {

        let entries_locs = {
            if params.len() == 2 {
                if params[1] < 1f64 {
                    Ok(calc_size_by_wrong_positives(params[0], params[1]))
                } else {
                    Ok(EntriesLocs {
                        entries: params[0] as u64,
                        locs: params[1] as u64,
                    })
                }
            } else {
                Err(RistrettoError::InvalidParams)
            }
        }?;

        let size = get_size(entries_locs.entries);

        let this = Self {
            bitset: vec![0; (size.size >> 6) as usize],
            elem_num: 0,
            size: size.size - 1,
            size_exp: size.exp,
            set_locs: entries_locs.locs,
            shift: 64 - size.exp
        };

        Ok(this)
    }

    /// `size` makes Bloom filter with as bitset of size sz.
    pub fn size(&mut self, sz: usize) {
        self.bitset = vec![0; sz >> 6]
    }

    /// `clear` resets the `Bloom` filter
    pub fn clear(&mut self) {
        self.bitset.iter_mut().for_each(|v| *v = 0);
    }

    /// `set` sets the bit[idx] of bitset
    pub fn set(&mut self, idx: usize) {
        let raw =  (addr_of!(self.bitset[idx >> 6]) as *const u64) as u64;
        let offset = ((idx % 64) >> 3) as u64;
        let ptr= (raw + offset) as *mut u64;
        unsafe {*ptr |= MASK[idx % 8] as u64;}
    }

    /// `is_set` checks if bit[idx] of bitset is set, returns true/false.
    pub fn is_set(&self, idx: usize) -> bool {
        let raw =  (addr_of!(self.bitset[idx >> 6]) as *const u64) as u64;
        let offset = ((idx % 64) >> 3) as u64;
        let ptr= (raw + offset) as *mut u64;
        unsafe {
            let r = (*ptr >> (idx % 8)) & 1;
            r == 1
        }
    }

    /// `add` adds hash of a key to the bloom filter
    pub fn add(&mut self, hash: u64) {
        let h = hash >> self.shift;
        let l = (hash << self.shift) >> self.shift;
        (0..self.set_locs).for_each(|i| {
            self.set(((h + i * l) & self.size) as usize);
            self.elem_num += 1;
        });
    }

    /// `has` checks if bit(s) for entry hash is/are set,
    /// returns true if the hash was added to the Bloom Filter.
    pub fn has(&self, hash: u64) -> bool {
        let h = hash >> self.shift;
        let l = (hash << self.shift) >> self.shift;
        for i in 0..self.set_locs {
            if !self.is_set(((h + i * l) & self.size) as usize) {
                return false;
            }
        }
        true
    }

    /// `add_if_not_has` only Adds hash, if it's not present in the bloomfilter.
    /// Returns true if hash was added.
    /// Returns false if hash was already registered in the bloomfilter.
    pub fn add_if_not_has(&mut self, hash: u64) -> bool {
        if self.has(hash) {
            false
        } else {
            self.add(hash);
            true
        }
    }

    /// `total_size` returns the total size of the bloom filter.
    pub fn total_size(&self) -> usize {
        // The bl struct has 5 members and each one is 8 byte. The bitset is a
        // uint64 byte slice.
        self.bitset.len() * 8 + 5 * 8
    }
}

#[cfg(test)]
mod test {
}