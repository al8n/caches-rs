use alloc::vec::Vec;

const DEPTH: usize = 4;

/// `CountMin` is a small conservative-update count-min sketch
/// implementation with 4-bit counters
struct CountMinSketch<const T: usize> {
    rows: [Vec<u8>; T],
    mask: u64,
}


// impl CountMinSketch<DEPTH> {
//     fn new(w: u64) -> Result<Self, LFUError> {
//         Ok()
//     }
// }

enum  LFUError {

}