use criterion::{black_box, criterion_group, criterion_main, Criterion};
use type_system::adt::{BinaryTree, List, Point};
use type_system::lambda_calculus::{LambdaCalculus, builder as lc};
use type_system::type_checker::{TypeChecker, TypeEnvironment, builder as tc};

fn bench_binary_tree(c: &mut Criterion) {
    c.bench_function("binary_tree_insert", |b| {
        b.iter(|| {
            let mut tree = BinaryTree::new(black_box(10));
            for i in 0..100 {
                tree.insert_left(black_box(i));
            }
            tree
        });
    });
    
    c.bench_function("binary_tree_traversal", |b| {
        let mut tree = BinaryTree::new(10);
        for i in 0..100 {
            tree.insert_left(i);
        }
        
        b.iter(|| {
            let mut result = Vec::new();
            tree.inorder_traversal(&mut result);
            result
        });
    });
}

fn bench_lambda_calculus(c: &mut Criterion) {
    c.bench_function("lambda_type_check", |b| {
        let lc = LambdaCalculus::new();
        let id = lc::abs("x", lc::int_ty(), lc::var("x"));
        
        b.iter(|| {
            lc.type_check(&id, &std::collections::HashMap::new())
        });
    });
    
    c.bench_function("lambda_eval", |b| {
        let lc = LambdaCalculus::new();
        let id = lc::abs("x", lc::int_ty(), lc::var("x"));
        let app = lc::app(id, lc::int(42));
        
        b.iter(|| {
            lc.eval(&app)
        });
    });
}

fn bench_type_checker(c: &mut Criterion) {
    c.bench_function("hindley_milner_infer", |b| {
        let mut tc = TypeChecker::new();
        let mut env = TypeEnvironment::new();
        let expr = tc::lambda("x", tc::var("x"));
        
        b.iter(|| {
            tc.infer(&expr, &mut env)
        });
    });
}

criterion_group!(benches, bench_binary_tree, bench_lambda_calculus, bench_type_checker);
criterion_main!(benches);
