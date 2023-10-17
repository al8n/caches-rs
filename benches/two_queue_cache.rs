use caches::{Cache, TwoQueueCache, TwoQueueCacheBuilder};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use fnv::FnvBuildHasher;
use rand::{thread_rng, Rng};
use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

fn bench_two_queue_cache_default_hasher(c: &mut Criterion) {
    c.bench_function("Test TwoQueueCache freq default hasher", move |b| {
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
                let l = TwoQueueCache::new(8192).unwrap();
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

fn bench_two_queue_cache_fx_hasher(c: &mut Criterion) {
    c.bench_function("Test TwoQueueCache freq FX hasher", move |b| {
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

                let builder = TwoQueueCacheBuilder::new(8192)
                    .set_recent_hasher(BuildHasherDefault::<FxHasher>::default())
                    .set_frequent_hasher(BuildHasherDefault::<FxHasher>::default())
                    .set_ghost_hasher(BuildHasherDefault::<FxHasher>::default());
                let l = TwoQueueCache::from_builder(builder).unwrap();
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

fn bench_two_queue_cache_fnv_hasher(c: &mut Criterion) {
    c.bench_function("Test TwoQueueCache freq FNV hasher", move |b| {
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
                let builder = TwoQueueCacheBuilder::new(8192)
                    .set_recent_hasher(FnvBuildHasher::default())
                    .set_frequent_hasher(FnvBuildHasher::default())
                    .set_ghost_hasher(FnvBuildHasher::default());
                let l = TwoQueueCache::from_builder(builder).unwrap();
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
    two_queue_cache,
    bench_two_queue_cache_default_hasher,
    bench_two_queue_cache_fx_hasher,
    bench_two_queue_cache_fnv_hasher
);

criterion_main!(two_queue_cache);
