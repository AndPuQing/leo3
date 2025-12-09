//! Benchmarks for Vec<T> ↔ LeanArray conversions
//!
//! This benchmarks the performance improvements from pre-allocation
//! and unchecked push operations.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use leo3::instance::LeanAny;
use leo3::prelude::*;

/// Naive implementation (for comparison) - uses regular push without pre-allocation
fn vec_to_array_naive<'l>(lean: Lean<'l>, vec: Vec<u64>) -> LeanResult<LeanBound<'l, LeanArray>> {
    let mut arr = LeanArray::empty(lean)?;

    for item in vec {
        let lean_item = LeanNat::from_usize(lean, item as usize)?;
        let any_item: LeanBound<'l, LeanAny> = lean_item.cast();
        arr = LeanArray::push(arr, any_item)?;
    }

    Ok(arr)
}

/// Optimized implementation - uses with_capacity + push_unchecked
fn vec_to_array_optimized<'l>(
    lean: Lean<'l>,
    vec: Vec<u64>,
) -> LeanResult<LeanBound<'l, LeanArray>> {
    let len = vec.len();

    if len == 0 {
        return LeanArray::empty(lean);
    }

    let mut arr = LeanArray::with_capacity(lean, len)?;

    for item in vec {
        let lean_item = LeanNat::from_usize(lean, item as usize)?;
        let any_item: LeanBound<'l, LeanAny> = lean_item.cast();
        arr = unsafe { LeanArray::push_unchecked(arr, any_item)? };
    }

    Ok(arr)
}

/// Benchmark converting Vec → LeanArray for different sizes
fn bench_vec_to_array(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    let mut group = c.benchmark_group("vec_to_array");

    for size in [10, 100, 1000, 10000].iter() {
        let vec: Vec<u64> = (0..*size).collect();

        group.bench_with_input(BenchmarkId::new("naive", size), size, |b, _| {
            b.iter(|| {
                leo3::with_lean(|lean| -> LeanResult<()> {
                    let v = vec.clone();
                    let arr = vec_to_array_naive(lean, black_box(v)).unwrap();
                    black_box(arr);
                    Ok(())
                })
                .unwrap();
            });
        });

        group.bench_with_input(BenchmarkId::new("optimized", size), size, |b, _| {
            b.iter(|| {
                leo3::with_lean(|lean| -> LeanResult<()> {
                    let v = vec.clone();
                    let arr = vec_to_array_optimized(lean, black_box(v)).unwrap();
                    black_box(arr);
                    Ok(())
                })
                .unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark converting LeanArray → Vec for different sizes
fn bench_array_to_vec(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    let mut group = c.benchmark_group("array_to_vec");

    for size in [10, 100, 1000, 10000].iter() {
        // Pre-create the array
        let arr = leo3::with_lean(|lean| -> LeanResult<_> {
            let mut arr = LeanArray::empty(lean)?;
            for i in 0..*size {
                let n = LeanNat::from_usize(lean, i)?;
                arr = LeanArray::push(arr, n.cast())?;
            }
            Ok(arr.unbind())
        })
        .unwrap();

        group.bench_with_input(BenchmarkId::new("with_prealloc", size), size, |b, _| {
            b.iter(|| {
                leo3::with_lean(|lean| -> LeanResult<()> {
                    let bound_arr = arr.bind(lean);
                    let vec: Vec<u64> =
                        leo3::conversion::FromLean::from_lean(&black_box(bound_arr)).unwrap();
                    black_box(vec);
                    Ok(())
                })
                .unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark round-trip conversion Vec → LeanArray → Vec
fn bench_roundtrip(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    let mut group = c.benchmark_group("roundtrip");

    for size in [10, 100, 1000].iter() {
        let vec: Vec<u64> = (0..*size).collect();

        group.bench_with_input(BenchmarkId::new("naive", size), size, |b, _| {
            b.iter(|| {
                leo3::with_lean(|lean| -> LeanResult<()> {
                    let v = vec.clone();
                    let arr = vec_to_array_naive(lean, black_box(v)).unwrap();
                    let result: Vec<u64> = leo3::conversion::FromLean::from_lean(&arr).unwrap();
                    black_box(result);
                    Ok(())
                })
                .unwrap();
            });
        });

        group.bench_with_input(BenchmarkId::new("optimized", size), size, |b, _| {
            b.iter(|| {
                leo3::with_lean(|lean| -> LeanResult<()> {
                    let v = vec.clone();
                    let arr = vec_to_array_optimized(lean, black_box(v)).unwrap();
                    let result: Vec<u64> = leo3::conversion::FromLean::from_lean(&arr).unwrap();
                    black_box(result);
                    Ok(())
                })
                .unwrap();
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_vec_to_array,
    bench_array_to_vec,
    bench_roundtrip
);
criterion_main!(benches);
