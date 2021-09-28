use caches::{AdaptiveCache, Cache, LRUCache, TwoQueueCache, WTinyLFUCache, SegmentedCache};
use rand::{thread_rng, Rng};
use rand::seq::SliceRandom;

extern crate cascara;

use cascara::{Cache as CascaraCache, OnEvict};
use std::time::Duration;

fn cascara_cache(cases: Vec<(usize, Vec<u64>)>) -> Vec<(usize, f64)> {
    let mut result: Vec<(usize, f64)> = Vec::with_capacity(cases.len());

    cases.iter().for_each(|total| {
        let mut l = CascaraCache::with_window_size(8110, 82);

        let mut hit = 0u64;
        let mut miss = 0u64;

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            let _ = l.insert(k, k);
        });

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            if let Some(_) = l.get(&k) {
                hit += 1;
            } else {
                miss += 1;
            }
        });

        let hit_ratio = ((hit as f64) / ((*total).0 as f64)) * 100.0;
        result.push(((*total).0, hit_ratio));
    });

    result
}


fn lru_cache(cases: Vec<(usize, Vec<u64>)>) -> Vec<(usize, f64)> {
    let mut result: Vec<(usize, f64)> = Vec::with_capacity(cases.len());

    cases.iter().for_each(|total| {
        let mut l = LRUCache::new(8192).unwrap();

        let mut hit = 0u64;
        let mut miss = 0u64;

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            let _ = l.put(k, k);
        });

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            if let Some(_) = l.get(&k) {
                hit += 1;
            } else {
                miss += 1;
            }
        });

        let hit_ratio = ((hit as f64) / ((*total).0 as f64)) * 100.0;
        result.push(((*total).0, hit_ratio));
    });

    result
}

fn two_queue_cache(cases: Vec<(usize, Vec<u64>)>) -> Vec<(usize, f64)> {
    let mut result: Vec<(usize, f64)> = Vec::with_capacity(cases.len());

    cases.iter().for_each(|total| {
        let mut l = TwoQueueCache::new(8192).unwrap();

        let mut hit = 0u64;
        let mut miss = 0u64;

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            let _ = l.put(k, k);
        });

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            if let Some(_) = l.get(&k) {
                hit += 1;
            } else {
                miss += 1;
            }
        });

        let hit_ratio = ((hit as f64) / ((*total).0 as f64)) * 100.0;
        result.push(((*total).0, hit_ratio));
    });

    result
}

fn arc_cache(cases: Vec<(usize, Vec<u64>)>) -> Vec<(usize, f64)> {
    let mut result: Vec<(usize, f64)> = Vec::with_capacity(cases.len());

    cases.iter().for_each(|total| {
        let mut l = AdaptiveCache::new(8192).unwrap();

        let mut hit = 0u64;
        let mut miss = 0u64;

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            let _ = l.put(k, k);
        });

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            if let Some(_) = l.get(&k) {
                hit += 1;
            } else {
                miss += 1;
            }
        });

        let hit_ratio = ((hit as f64) / ((*total).0 as f64)) * 100.0;
        result.push(((*total).0, hit_ratio));
    });

    result
}

fn segmented_cache(cases: Vec<(usize, Vec<u64>)>) -> Vec<(usize, f64)> {
    let mut result: Vec<(usize, f64)> = Vec::with_capacity(cases.len());

    cases.iter().for_each(|total| {
        let mut l = SegmentedCache::new(1638, 6554).unwrap();

        let mut hit = 0u64;
        let mut miss = 0u64;

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            let _ = l.put(k, k);
        });

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            if let Some(_) = l.get(&k) {
                hit += 1;
            } else {
                miss += 1;
            }
        });

        let hit_ratio = ((hit as f64) / ((*total).0 as f64)) * 100.0;
        result.push(((*total).0, hit_ratio));
    });

    result
}

fn wtinylfu_cache(cases: Vec<(usize, Vec<u64>)>) -> Vec<(usize, f64)> {
    let mut result: Vec<(usize, f64)> = Vec::with_capacity(cases.len());

    cases.iter().for_each(|total| {
        let mut l = WTinyLFUCache::with_sizes(82, 6488, 1622, 8192).unwrap();

        let mut hit = 0u64;
        let mut miss = 0u64;

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            let _ = l.put(k, k);
        });

        (0..(*total).0).for_each(|v| {
            let k = (*total).1[v];
            if let Some(_) = l.get(&k) {
                hit += 1;
            } else {
                miss += 1;
            }
        });

        let hit_ratio = ((hit as f64) / ((*total).0 as f64)) * 100.0;
        result.push(((*total).0, hit_ratio));
    });

    result
}

fn main() {
    let cases: Vec<usize> = [100_0000].to_vec();
    let random_numbers: Vec<(usize, Vec<u64>)> = cases
        .iter()
        .map(|total| {
            let total = *total;
            let mut rng = thread_rng();
            let freq_nums: Vec<Vec<u64>> = (0..100u64).map(|i| {
                let ctrs = rng.gen::<u8>() as u64;
                vec![i; (i * ctrs) as usize]
            }).collect();

            let mut nums = Vec::with_capacity(total);
            freq_nums.into_iter().for_each(|v| {
               nums.extend(v);
            });

            let random_nums: Vec<u64> = (0..(total - nums.len()) * 2)
                .map(|i| {
                    if i % 2 == 0 {
                        rng.gen::<u64>() % 16384
                    } else {
                        rng.gen::<u64>() % 32768
                    }
                })
                .collect();
            nums.extend(random_nums);
            nums.shuffle(&mut rng);
            (total, nums)
        })
        .collect();

    println!("LRU Hit Ratio: {:?}", lru_cache(random_numbers.clone()));
    println!(
        "TwoQueueCache Hit Ratio: {:?}",
        two_queue_cache(random_numbers.clone())
    );
    println!(
        "AdaptiveCache Hit Ratio: {:?}",
        arc_cache(random_numbers.clone())
    );
    println!(
        "SegmentedCache Hit Ratio: {:?}",
        segmented_cache(random_numbers.clone())
    );

    println!(
        "WTinyLFUCache Hit Ratio: {:?}",
        wtinylfu_cache(random_numbers.clone())
    );

    println!(
        "CascaraCache Hit Ratio: {:?}",
        cascara_cache(random_numbers.clone())
    );
}
