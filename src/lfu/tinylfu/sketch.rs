use crate::{cfg_not_std, cfg_std};

mod count_min_row;
pub(crate) use count_min_row::CountMinRow;

cfg_std!(
    mod count_min_sketch_std;
    pub(crate) use count_min_sketch_std::CountMinSketch;
);

cfg_not_std!(
    mod count_min_sketch_core;
    pub(crate) use count_min_sketch_core::CountMinSketch;
);

const DEPTH: usize = 4;

// return the integer >= i which is a power of two
fn next_power_of_2(num: u64) -> u64 {
    let mut num = num - 1;
    num |= num >> 1;
    num |= num >> 2;
    num |= num >> 4;
    num |= num >> 8;
    num |= num >> 16;
    num += 1;
    num
}
