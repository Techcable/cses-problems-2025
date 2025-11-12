//! What is the most efficient way to compute binomial coefficients?
//!
//! Result: The multiplicative method is orders of magnitude faster than the recursive method.
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

/// Compute the binomial coefficient using recursion,
/// similar to using pascal's triangle.
fn recursive_binomial_coefficient(n: u32, k: u32) -> u128 {
    assert!(k <= n);
    if k == 0 || k == n {
        1
    } else {
        recursive_binomial_coefficient(n - 1, k - 1) + recursive_binomial_coefficient(n - 1, k)
    }
}

/// Compute the binomial coefficient the "obvious" way,
/// using multiplication.
///
/// https://en.wikipedia.org/wiki/Binomial_coefficient#Multiplicative_formula
pub fn binomial_coefficient(n: u32, k: u32) -> u64 {
    assert!(k <= n);
    fn fold(acc: u64, item: u32) -> u64 {
        acc * item as u64
    }
    if n == k || k == 0 {
        1
    } else {
        let num = ((n - k + 1)..=n).fold(1, fold);
        let denom = (1..=k).fold(1, fold);
        num / denom
    }
}

fn bench_binomials(c: &mut Criterion) {
    let mut group = c.benchmark_group("binomial_coefficients");
    const INPUTS: &[(u32, &[u32])] = &[(10, &[8]), (50, &[30]), (100, &[15, 50, 85])];
    let flattened_inputs = INPUTS
        .iter()
        .copied()
        .flat_map(|(n, possible_k)| possible_k.iter().copied().map(move |k| (n, k)));
    for (n, k) in flattened_inputs {
        let desc = format!("n={n}, k={k}");
        group.bench_with_input(
            BenchmarkId::new("multiplicative", &desc),
            &(n, k),
            |b, &(n, k)| b.iter(|| multiplicative_binomial_coefficient(n, k)),
        );
        group.bench_with_input(
            BenchmarkId::new("recursive", &desc),
            &(n, k),
            |b, &(n, k)| b.iter(|| recursive_binomial_coefficient(n, k)),
        );
    }
    group.finish();
}

criterion_group!(benches, bench_binomials);
criterion_main!(benches);
