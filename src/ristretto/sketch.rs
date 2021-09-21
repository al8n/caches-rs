use alloc::vec::Vec;

const DEPTH: usize = 4;

/// `CountMin` is a small conservative-update count-min sketch
/// implementation with 4-bit counters
struct CountMinSketch<const T: usize> {
    rows: [Vec<u8>; T],
    seed: [u64; T],
    mask: u64,
}



// impl CountMinSketch<DEPTH> {
//     fn new(ctrs: u64) -> Self {
//
//     }
// }
//
// fn next_power_of_2() -> u64 {
//
// }