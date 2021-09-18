use rand::{thread_rng, Rng};
use hashicorp_lru::{AdaptiveCache, TwoQueueCache, LRUCache};


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

fn main() {
    let cases: Vec<usize> = [10_000, 100_000, 200_000, 500_000, 1000_000].to_vec();
    let random_numbers: Vec<(usize, Vec<u64>)> = cases.iter().map(|total| {
        let total = *total;
        let mut rng = thread_rng();
        let nums: Vec<u64> = (0..(total * 2))
            .map(|i| {
                if i % 2 == 0 {
                    rng.gen::<u64>() % 16384
                } else {
                    rng.gen::<u64>() % 32768
                }
            })
            .collect();
        (total, nums)
    }).collect();


    println!("LRU Hit Ratio: {:?}", lru_cache(random_numbers.clone()));
    println!("TwoQueueCache Hit Ratio: {:?}", two_queue_cache(random_numbers.clone()));
    println!("AdaptiveCache Hit Ratio: {:?}", arc_cache(random_numbers.clone()));
}