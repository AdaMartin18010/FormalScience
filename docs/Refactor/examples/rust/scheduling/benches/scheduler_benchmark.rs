use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use scheduling::thread_pool::{ThreadPool, parallel_map, parallel_for};
use scheduling::work_stealing::WorkStealingPool;
use scheduling::priority_scheduler::PriorityScheduler;
use std::time::Duration;

fn bench_thread_pool(c: &mut Criterion) {
    let pool = ThreadPool::new(4);
    
    c.bench_function("thread_pool_spawn", |b| {
        b.iter(|| {
            for i in 0..100 {
                pool.execute(move || {
                    black_box(i * i);
                });
            }
        });
    });
}

fn bench_work_stealing(c: &mut Criterion) {
    let pool = WorkStealingPool::new(4);
    
    let mut group = c.benchmark_group("work_stealing");
    group.throughput(Throughput::Elements(100));
    
    group.bench_function("spawn_tasks", |b| {
        b.iter(|| {
            for i in 0..100 {
                pool.spawn(move || {
                    black_box(i * i);
                });
            }
        });
    });
    
    group.finish();
}

fn bench_priority_scheduler(c: &mut Criterion) {
    let scheduler = PriorityScheduler::new(4);
    
    c.bench_function("priority_spawn", |b| {
        b.iter(|| {
            for i in 0..100 {
                scheduler.spawn(move || {
                    black_box(i * i);
                });
            }
        });
    });
}

fn bench_parallel_map(c: &mut Criterion) {
    let data: Vec<i32> = (0..10000).collect();
    
    let mut group = c.benchmark_group("parallel_map");
    group.throughput(Throughput::Elements(data.len() as u64));
    
    group.bench_function("4_threads", |b| {
        b.iter(|| {
            parallel_map(black_box(data.clone()), |x| x * x, 4)
        });
    });
    
    group.bench_function("8_threads", |b| {
        b.iter(|| {
            parallel_map(black_box(data.clone()), |x| x * x, 8)
        });
    });
    
    group.finish();
}

fn bench_parallel_for(c: &mut Criterion) {
    c.bench_function("parallel_for_1000", |b| {
        b.iter(|| {
            parallel_for(0..1000, |i| {
                black_box(i * i);
            }, 4);
        });
    });
}

criterion_group!(benches, bench_thread_pool, bench_work_stealing, bench_priority_scheduler, bench_parallel_map, bench_parallel_for);
criterion_main!(benches);
