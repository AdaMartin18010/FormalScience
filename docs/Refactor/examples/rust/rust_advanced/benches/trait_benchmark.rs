use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rust_advanced::traits::{Complex, Vector2, VectorSpace};
use rust_advanced::zero_cost::{fast_sqrt, Vec4, BitSet};

fn bench_vector_operations(c: &mut Criterion) {
    c.bench_function("vector_add", |b| {
        let v1 = Vector2 { x: 1.0, y: 2.0 };
        let v2 = Vector2 { x: 3.0, y: 4.0 };
        
        b.iter(|| {
            black_box(v1.add(&v2))
        });
    });
    
    c.bench_function("vector_scale", |b| {
        let v = Vector2 { x: 1.0, y: 2.0 };
        
        b.iter(|| {
            black_box(v.scale(black_box(2.0)))
        });
    });
}

fn bench_complex_operations(c: &mut Criterion) {
    c.bench_function("complex_multiply", |b| {
        let c1 = Complex::new(1.0, 2.0);
        let c2 = Complex::new(3.0, 4.0);
        
        b.iter(|| {
            black_box(c1 * c2)
        });
    });
}

fn bench_bitset(c: &mut Criterion) {
    c.bench_function("bitset_operations", |b| {
        let mut bs: BitSet<1000> = BitSet::new();
        
        b.iter(|| {
            for i in 0..100 {
                bs.set(black_box(i));
            }
            for i in 0..100 {
                black_box(bs.get(i));
            }
            bs.clear_all();
        });
    });
}

fn bench_vec4(c: &mut Criterion) {
    c.bench_function("vec4_dot", |b| {
        let v1 = Vec4::new(1.0, 2.0, 3.0, 4.0);
        let v2 = Vec4::new(2.0, 3.0, 4.0, 5.0);
        
        b.iter(|| {
            black_box(v1.dot(v2))
        });
    });
    
    c.bench_function("vec4_normalize", |b| {
        let v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        
        b.iter(|| {
            black_box(v.normalize())
        });
    });
}

criterion_group!(benches, bench_vector_operations, bench_complex_operations, bench_bitset, bench_vec4);
criterion_main!(benches);
