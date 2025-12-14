//! Benchmarks for small Lean integer operations
//!
//! These benchmarks test operations on small integers (within i32 range)
//! that use the scalar fast path in lean_int_* functions.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use leo3::prelude::*;

/// Benchmark addition of small integers
fn bench_int_add_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_add_small_positive", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(12345))?;
                let b = LeanInt::from_i64(lean, black_box(67890))?;
                let result = LeanInt::add(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_add_small_mixed", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(-5000))?;
                let b = LeanInt::from_i64(lean, black_box(10000))?;
                let result = LeanInt::add(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark subtraction of small integers
fn bench_int_sub_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_sub_small_positive", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(100000))?;
                let b = LeanInt::from_i64(lean, black_box(42000))?;
                let result = LeanInt::sub(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_sub_small_negative_result", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(1000))?;
                let b = LeanInt::from_i64(lean, black_box(5000))?;
                let result = LeanInt::sub(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_sub_small_mixed_signs", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(-1000))?;
                let b = LeanInt::from_i64(lean, black_box(2000))?;
                let result = LeanInt::sub(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark multiplication of small integers
fn bench_int_mul_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_mul_small_positive", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(123))?;
                let b = LeanInt::from_i64(lean, black_box(456))?;
                let result = LeanInt::mul(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_mul_small_negative", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(-123))?;
                let b = LeanInt::from_i64(lean, black_box(456))?;
                let result = LeanInt::mul(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark division of small integers
fn bench_int_div_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_div_small_exact", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(100000))?;
                let b = LeanInt::from_i64(lean, black_box(100))?;
                let result = LeanInt::div(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_div_small_remainder", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(123456))?;
                let b = LeanInt::from_i64(lean, black_box(789))?;
                let result = LeanInt::div(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark modulus of small integers
fn bench_int_mod_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_mod_small", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(123456))?;
                let b = LeanInt::from_i64(lean, black_box(789))?;
                let result = LeanInt::mod_(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark Euclidean division and modulus
fn bench_int_euclidean_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_ediv_small", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(-12345))?;
                let b = LeanInt::from_i64(lean, black_box(67))?;
                let result = LeanInt::ediv(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_emod_small", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(-12345))?;
                let b = LeanInt::from_i64(lean, black_box(67))?;
                let result = LeanInt::emod(&a, &b)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark comparisons
fn bench_int_comparisons_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_eq_small", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(12345))?;
                let b = LeanInt::from_i64(lean, black_box(12345))?;
                let result = LeanInt::eq(&a, &b);
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_lt_small", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(12345))?;
                let b = LeanInt::from_i64(lean, black_box(67890))?;
                let result = LeanInt::lt(&a, &b);
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_le_small", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(12345))?;
                let b = LeanInt::from_i64(lean, black_box(67890))?;
                let result = LeanInt::le(&a, &b);
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark negation
fn bench_int_neg_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_neg_small_positive", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(12345))?;
                let result = LeanInt::neg(a)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_neg_small_negative", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(-12345))?;
                let result = LeanInt::neg(a)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });
}

/// Benchmark common operation chains
fn bench_int_chains_small(c: &mut Criterion) {
    leo3::prepare_freethreaded_lean();

    c.bench_function("int_chain_add_sub", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(1000))?;
                let b = LeanInt::from_i64(lean, black_box(2000))?;
                let c = LeanInt::from_i64(lean, black_box(500))?;

                // (a + b) - c
                let sum = LeanInt::add(&a, &b)?;
                let result = LeanInt::sub(&sum, &c)?;
                black_box(result);
                Ok(())
            })
            .unwrap();
        });
    });

    c.bench_function("int_chain_mul_div", |b| {
        b.iter(|| {
            leo3::with_lean(|lean| -> LeanResult<()> {
                let a = LeanInt::from_i64(lean, black_box(100))?;
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
    bench_int_add_small,
    bench_int_sub_small,
    bench_int_mul_small,
    bench_int_div_small,
    bench_int_mod_small,
    bench_int_euclidean_small,
    bench_int_comparisons_small,
    bench_int_neg_small,
    bench_int_chains_small,
);
criterion_main!(benches);
