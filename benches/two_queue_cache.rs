// use hashicorp_lru::TwoQueueCache;
// use rand::{thread_rng, Rng};
// use criterion::{Criterion, BenchmarkId, criterion_group, criterion_main, black_box};
//
// fn bench_2q_cache_freq(c: &mut Criterion) {
//     let mut l = TwoQueueCache::new(8192).unwrap();
//     let mut rng = thread_rng();
//     let cases = 1000_000;
//     let nums: Vec<i64> = black_box((0..(cases * 2)).map(|i| {
//         if i % 2 == 0 {
//             rng.gen::<i64>() % 16384
//         } else {
//             rng.gen::<i64>() % 32768
//         }
//     }).collect());
//
//     let mut hit = black_box(0u64);
//     let mut miss = black_box(0u64);
//
//     c.bench_with_input(BenchmarkId::new("Test TwoQueueCache freq", "1000_000"), &nums, |b, i| b.iter( || {
//         (0..cases).for_each(|v| {
//             let k  = i[v];
//             let _ = l.put(k, k);
//         });
//
//         (0..cases).for_each(|v| {
//             let k  = i[v];
//             match l.get(&k) {
//                 None => miss +=1,
//                 Some(_) => hit += 1,
//             };
//         })
//     }));
//
//
//     println!("hit: {}, miss: {}, ratio: {}", hit, miss, hit as f64 / miss as f64);
// }
//
// criterion_group!(two_queue_cache);
//
// criterion_main!(two_queue_cache);