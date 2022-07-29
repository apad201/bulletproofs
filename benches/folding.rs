#![allow(non_snake_case)]
#![feature(bench_black_box)]


#[macro_use]
extern crate criterion;

use std::hint::black_box;
use std::iter;

use criterion::Criterion;
use criterion::BenchmarkId;
use bulletproofs::{ZKMatrixFoldingProof, get_gens, tp_mat_mult};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

fn prove_square_folding(crit: &mut Criterion) {

    let mut group = crit.benchmark_group("prove_square_folding");
    for size in [1,2,4,8,16, 32, 64].iter().map(|x| *x as usize) {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size,
        |bench, &size| {
            let (G, H, U, g_0) = get_gens(size, size, size);
            let mut rng = rand::thread_rng();
            let a: Vec<_> = (0..(size*size)).map(|_| Scalar::random(&mut rng)).collect();
            let b: Vec<_> = (0..(size*size)).map(|_| Scalar::random(&mut rng)).collect();
            let r = Scalar::random(&mut rng);
            bench.iter(|| {
                let mut prover = Transcript::new(b"matrixfoldingbench");
                let proof = ZKMatrixFoldingProof::create(
                    &mut prover,
                    black_box(G.clone()),
                    black_box(H.clone()),
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

fn verify_square_folding(crit: &mut Criterion) {
    let mut group = crit.benchmark_group("verify_square_folding");
    for size in [1,2,4,8,16,32,64].iter().map(|x| *x as usize) {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size,
        |bench, &size| {
            let mut rng = rand::thread_rng();
            let (G, H, U, g_0) = get_gens(size, size, size);
            let a: Vec<_> = (0..(size*size)).map(|_| Scalar::random(&mut rng)).collect();
            let b: Vec<_> = (0..(size*size)).map(|_| Scalar::random(&mut rng)).collect();
            let c = tp_mat_mult(&a, &b, size, size);
            let r = Scalar::random(&mut rng);
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
            let P = RistrettoPoint::vartime_multiscalar_mul(
                a.iter()
                    .chain(b.iter())
                    .chain(c.iter())
                    .chain(iter::once(&r)),
                G.iter()
                    .chain(H.iter())
                    .chain(U.iter())
                    .chain(iter::once(&g_0))
            );
            bench.iter(|| {
                let mut verifier = Transcript::new(b"matrixfoldingbench");
                assert!(proof.verify(
                    &mut verifier,
                    &P,
                    &G[..],
                    &H[..],
                    &U[..],
                    &g_0,
                    size,
                    size,
                    size
                ).is_ok());
            });
        });
    }
    group.finish();

}

criterion_group!(folding_prove, prove_square_folding);

criterion_group!(folding_verify, verify_square_folding);

criterion_main!(folding_prove, folding_verify);