#![allow(non_snake_case)]


#[macro_use]
extern crate criterion;

use criterion::Criterion;
use criterion::BenchmarkId;
use bulletproofs::{ZKMatrixFoldingProof, get_gens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;



fn square_fold(c: &mut Criterion) {
    let mut group = c.benchmark_group("square_fold");
    for size in [1,2,4,8,16, 32, 64].iter().map(|x| *x as usize) {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size,
        |bench, &size| {
            let mut rng = rand::thread_rng();
            let (G, H, U, g_0) = get_gens(size, size, size);
            let a: Vec<_> = (0..(size*size)).map(|_| Scalar::random(&mut rng)).collect();
            let b: Vec<_> = (0..(size*size)).map(|_| Scalar::random(&mut rng)).collect();
            let r = Scalar::random(&mut rng);

            bench.iter(|| {
                let mut prover = Transcript::new(b"matrixfoldingbench");
                let proof = ZKMatrixFoldingProof::create(
                    &mut prover,
                    G.clone(),
                    H.clone(),
                    U.clone(),
                    g_0.clone(),
                    a.clone(),
                    b.clone(),
                    r.clone(),
                    size,
                    size,
                    size
                );
                proof
            });
        });
    }
    group.finish();

}

criterion_group!(folding, square_fold);

criterion_main!(folding);