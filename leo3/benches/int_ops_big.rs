//! Benchmarks for big Lean integer operations
//!
//! These benchmarks test operations on big integers (beyond i32 range)
//! that use the big integer slow path in lean_int_* functions.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use leo3::prelude::*;
use std::hint::black_box;

/// Create a large integer beyond i32::MAX
fn create_large_int(lean: Lean, multiplier: i64) -> LeanResult<LeanBound<LeanInt>> {
    LeanInt::from_i64(lean, (i32::MAX as i64) + multiplier)
}

/// Benchmark addition of big integers
fn bench_int_add_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_add_big_both_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = create_large_int(lean, black_box(2000000))?;
                let result = LeanInt::add(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_add_big_one_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = LeanInt::from_i64(lean, black_box(5000))?;
                let result = LeanInt::add(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_add_big_very_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(i64::MAX / 2))?;
                let b = LeanInt::from_i64(lean, black_box(i64::MAX / 4))?;
                let result = LeanInt::add(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark subtraction of big integers
fn bench_int_sub_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_sub_big_both_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(3000000))?;
                let b = create_large_int(lean, black_box(1000000))?;
                let result = LeanInt::sub(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_sub_big_one_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = LeanInt::from_i64(lean, black_box(5000))?;
                let result = LeanInt::sub(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_sub_big_very_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(i64::MAX / 2))?;
                let b = LeanInt::from_i64(lean, black_box(i64::MAX / 4))?;
                let result = LeanInt::sub(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_sub_big_crossing_threshold", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                // Result becomes small
                let a = create_large_int(lean, black_box(1000))?;
                let b = create_large_int(lean, black_box(500))?;
                let result = LeanInt::sub(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark multiplication of big integers
fn bench_int_mul_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_mul_big_both_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(10000))?;
                let b = create_large_int(lean, black_box(20000))?;
                let result = LeanInt::mul(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_mul_big_one_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(10000))?;
                let b = LeanInt::from_i64(lean, black_box(123))?;
                let result = LeanInt::mul(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_mul_big_medium_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(i32::MAX as i64 / 2))?;
                let b = LeanInt::from_i64(lean, black_box(100))?;
                let result = LeanInt::mul(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark division of big integers
fn bench_int_div_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_div_big_both_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = create_large_int(lean, black_box(1000))?;
                let result = LeanInt::div(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_div_big_one_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = LeanInt::from_i64(lean, black_box(789))?;
                let result = LeanInt::div(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_div_big_very_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(i64::MAX / 2))?;
                let b = LeanInt::from_i64(lean, black_box(i32::MAX as i64))?;
                let result = LeanInt::div(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark modulus of big integers
fn bench_int_mod_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_mod_big_both_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = create_large_int(lean, black_box(789))?;
                let result = LeanInt::mod_(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_mod_big_one_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = LeanInt::from_i64(lean, black_box(789))?;
                let result = LeanInt::mod_(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark Euclidean operations on big integers
fn bench_int_euclidean_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_ediv_big", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = LeanInt::from_i64(lean, black_box(789))?;
                let result = LeanInt::ediv(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_emod_big", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = LeanInt::from_i64(lean, black_box(789))?;
                let result = LeanInt::emod(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark comparisons with big integers
fn bench_int_comparisons_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_eq_big", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = create_large_int(lean, black_box(1000000))?;
                let result = LeanInt::eq(&a, &b);
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_lt_big", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = create_large_int(lean, black_box(2000000))?;
                let result = LeanInt::lt(&a, &b);
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_le_big", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = create_large_int(lean, black_box(2000000))?;
                let result = LeanInt::le(&a, &b);
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark negation of big integers
fn bench_int_neg_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_neg_big", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let result = LeanInt::neg(a)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_neg_big_very_large", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(i64::MAX / 2))?;
                let result = LeanInt::neg(a)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark scaling (different sizes of big integers)
fn bench_int_scaling(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    let mut group = c.benchmark_group("int_add_scaling");

    for size_mult in [1_000, 10_000, 100_000, 1_000_000].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(size_mult),
            size_mult,
            |b, &mult| {
                b.iter(|| {
                    leo3::with_lean(|lean| -> LeanResult<()> {
                        let a = create_large_int(lean, black_box(mult))?;
                        let b = create_large_int(lean, black_box(mult / 2))?;
                        let result = LeanInt::add(&a, &b)?;
                        black_box(result);
                        Ok(())
                    })
                    .unwrap();
                });
            },
        );
    }

    group.finish();

    let mut group = c.benchmark_group("int_sub_scaling");

    for size_mult in [1_000, 10_000, 100_000, 1_000_000].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(size_mult),
            size_mult,
            |b, &mult| {
                b.iter(|| {
                    leo3::with_lean(|lean| -> LeanResult<()> {
                        let a = create_large_int(lean, black_box(mult))?;
                        let b = create_large_int(lean, black_box(mult / 2))?;
                        let result = LeanInt::sub(&a, &b)?;
                        black_box(result);
                        Ok(())
                    })
                    .unwrap();
                });
            },
        );
    }

    group.finish();

    let mut group = c.benchmark_group("int_mul_scaling");

    for size_mult in [1_000, 10_000, 100_000].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(size_mult),
            size_mult,
            |b, &mult| {
                b.iter(|| {
                    leo3::with_lean(|lean| -> LeanResult<()> {
                        let a = create_large_int(lean, black_box(mult))?;
                        let b = LeanInt::from_i64(lean, black_box(100))?;
                        let result = LeanInt::mul(&a, &b)?;
                        black_box(result);
                        Ok(())
                    })
                    .unwrap();
                });
            },
        );
    }

    group.finish();
}

/// Benchmark common operation chains with big integers
fn bench_int_chains_big(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_chain_big_add_sub", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(1000000))?;
                let b = create_large_int(lean, black_box(2000000))?;
                let c = create_large_int(lean, black_box(500000))?;

                // (a + b) - c
                let sum = LeanInt::add(&a, &b)?;
                let result = LeanInt::sub(&sum, &c)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_chain_big_mul_div", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = create_large_int(lean, black_box(10000))?;
                let b = LeanInt::from_i64(lean, black_box(200))?;
                let c = LeanInt::from_i64(lean, black_box(5))?;

                // (a * b) / c
                let prod = LeanInt::mul(&a, &b)?;
                let result = LeanInt::div(&prod, &c)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

criterion_group!(
    benches,
    bench_int_add_big,
    bench_int_sub_big,
    bench_int_mul_big,
    bench_int_div_big,
    bench_int_mod_big,
    bench_int_euclidean_big,
    bench_int_comparisons_big,
    bench_int_neg_big,
    bench_int_scaling,
    bench_int_chains_big,
);
criterion_main!(benches);
