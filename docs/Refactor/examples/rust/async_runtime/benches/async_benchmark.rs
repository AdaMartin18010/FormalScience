use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_async(c: &mut Criterion) {
    c.bench_function("simple_async", |b| {
        b.iter(|| {
            black_box(42)
        });
    });
}

criterion_group!(benches, bench_async);
criterion_main!(benches);
