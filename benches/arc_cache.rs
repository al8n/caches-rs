use caches::{AdaptiveCache, AdaptiveCacheBuilder, Cache};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use fnv::FnvBuildHasher;
use rand::{thread_rng, Rng};
use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

fn bench_arc_cache_default_hasher(c: &mut Criterion) {
    c.bench_function("Test AdaptiveCache freq default hasher", move |b| {
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
                let l = AdaptiveCache::new(8192).unwrap();
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

fn bench_arc_cache_fx_hasher(c: &mut Criterion) {
    c.bench_function("Test AdaptiveCache freq FX hasher", move |b| {
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

                let builder = AdaptiveCacheBuilder::new(8192)
                    .set_recent_hasher(BuildHasherDefault::<FxHasher>::default())
                    .set_frequent_hasher(BuildHasherDefault::<FxHasher>::default())
                    .set_recent_evict_hasher(BuildHasherDefault::<FxHasher>::default())
                    .set_frequent_evict_hasher(BuildHasherDefault::<FxHasher>::default());
                let l = AdaptiveCache::from_builder(builder).unwrap();
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

fn bench_arc_cache_fnv_hasher(c: &mut Criterion) {
    c.bench_function("Test AdaptiveCache freq FNV hasher", move |b| {
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
                let builder = AdaptiveCacheBuilder::new(8192)
                    .set_recent_hasher(FnvBuildHasher::default())
                    .set_frequent_hasher(FnvBuildHasher::default())
                    .set_recent_evict_hasher(FnvBuildHasher::default())
                    .set_frequent_evict_hasher(FnvBuildHasher::default());
                let l = AdaptiveCache::from_builder(builder).unwrap();
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
    arc_cache,
    bench_arc_cache_default_hasher,
    bench_arc_cache_fx_hasher,
    bench_arc_cache_fnv_hasher
);

criterion_main!(arc_cache);
