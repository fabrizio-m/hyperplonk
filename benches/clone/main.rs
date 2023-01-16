use ark_bls12_381::Fr;
use ark_ff::UniformRand;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::thread_rng;

pub fn criterion_benchmark(c: &mut Criterion) {
    //c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
    let mut group = c.benchmark_group("clone");
    for i in 0..16 {
        let mut rng = thread_rng();
        let data: Vec<Fr> = (0..(1 << i)).map(|_| Fr::rand(&mut rng)).collect();

        group.bench_with_input(BenchmarkId::from_parameter(format!("2^{i}")), &i, |b, _| {
            // c.bench_with_input(BenchmarkId::new("clone 2^", i), &i, |b, _| {
            b.iter_with_large_drop(|| {
                let a = data.clone();
                a
            });
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
