use caches::{Cache, SegmentedCache, SegmentedCacheBuilder};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use fnv::FnvBuildHasher;
use rand::{thread_rng, Rng};
use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

fn bench_segmented_cache_default_hasher(c: &mut Criterion) {
    c.bench_function("Test SegmentedCache freq default hasher", move |b| {
        let cases = 1_000_000;
        b.iter_batched(
            || {
                let mut rng = thread_rng();
                let nums: Vec<u64> = black_box(
                    (0..(cases * 2))
                        .map(|i| {
                            if i % 2 == 0 {
                                rng.gen::<u64>() % 16384
                            } else {
                                rng.gen::<u64>() % 32768
                            }
                        })
                        .collect(),
                );
                let l = SegmentedCache::new(1638, 6554).unwrap();
                (l, nums)
            },
            |(mut l, nums)| {
                (0..cases).for_each(|v| {
                    let k = nums[v];
                    let _ = l.put(k, k);
                });

                (0..cases).for_each(|v| {
                    let k = nums[v];
                    let _ = l.get(&k);
                });
            },
            BatchSize::LargeInput,
        )
    });
}

fn bench_segmented_cache_fx_hasher(c: &mut Criterion) {
    c.bench_function("Test SegmentedCache freq FX hasher", move |b| {
        let cases = 1_000_000;
        b.iter_batched(
            || {
                let mut rng = thread_rng();
                let nums: Vec<u64> = black_box(
                    (0..(cases * 2))
                        .map(|i| {
                            if i % 2 == 0 {
                                rng.gen::<u64>() % 16384
                            } else {
                                rng.gen::<u64>() % 32768
                            }
                        })
                        .collect(),
                );

                let builder = SegmentedCacheBuilder::new(1638, 6554)
                    .set_probationary_hasher(BuildHasherDefault::<FxHasher>::default())
                    .set_protected_hasher(BuildHasherDefault::<FxHasher>::default());
                let l = SegmentedCache::from_builder(builder).unwrap();
                (l, nums)
            },
            |(mut l, nums)| {
                (0..cases).for_each(|v| {
                    let k = nums[v];
                    let _ = l.put(k, k);
                });

                (0..cases).for_each(|v| {
                    let k = nums[v];
                    let _ = l.get(&k);
                });
            },
            BatchSize::LargeInput,
        )
    });
}

fn bench_segmented_cache_fnv_hasher(c: &mut Criterion) {
    c.bench_function("Test SegmentedCache freq FNV hasher", move |b| {
        let cases = 1_000_000;
        b.iter_batched(
            || {
                let mut rng = thread_rng();
                let nums: Vec<u64> = black_box(
                    (0..(cases * 2))
                        .map(|i| {
                            if i % 2 == 0 {
                                rng.gen::<u64>() % 16384
                            } else {
                                rng.gen::<u64>() % 32768
                            }
                        })
                        .collect(),
                );
                let builder = SegmentedCacheBuilder::new(1638, 6554)
                    .set_probationary_hasher(FnvBuildHasher::default())
                    .set_protected_hasher(FnvBuildHasher::default());
                let l = SegmentedCache::from_builder(builder).unwrap();
                (l, nums)
            },
            |(mut l, nums)| {
                (0..cases).for_each(|v| {
                    let k = nums[v];
                    let _ = l.put(k, k);
                });

                (0..cases).for_each(|v| {
                    let k = nums[v];
                    let _ = l.get(&k);
                });
            },
            BatchSize::LargeInput,
        )
    });
}

criterion_group!(
    segmented_cache,
    bench_segmented_cache_default_hasher,
    bench_segmented_cache_fx_hasher,
    bench_segmented_cache_fnv_hasher
);

criterion_main!(segmented_cache);
