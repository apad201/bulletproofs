#![allow(non_snake_case)]
#![feature(bench_black_box)]


#[macro_use]
extern crate criterion;

use std::iter;

use criterion::{Criterion, SamplingMode};
use bulletproofs::{ZKMatrixFoldingProof, get_gens, tp_mat_mult};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

fn prove_square_folding(crit: &mut Criterion) {

    let mut group = crit.benchmark_group("prove_square_folding");
    group.sampling_mode(SamplingMode::Flat);
    let range = [1,2,4,8,16,32,64];
    for n in range.iter().map(|x| *x as usize) {
        for m in range.iter().map(|x| *x as usize) {
            for k in range.iter().map(|x| *x as usize) {
                let id = format!("{},{},{}", n,m,k);
                group.bench_with_input(&id, &(n,m,k),
                |bench, &(n,m,k)| {
                    let (G, H, U, g_0) = get_gens(n, m, k);
                    let mut rng = rand::thread_rng();
                    let a: Vec<_> = (0..(n * m)).map(|_| Scalar::random(&mut rng)).collect();
                    let b: Vec<_> = (0..(m * k)).map(|_| Scalar::random(&mut rng)).collect();
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
                            n,
                            m,
                            k
                        );
                        proof
                    });
                });
            }
        }
        
    }
    group.finish();

}

fn verify_square_folding(crit: &mut Criterion) {
    let mut group = crit.benchmark_group("verify_square_folding");
    group.sampling_mode(SamplingMode::Flat);
    let range = [1,2,4,8,16,32,64];
    for n in range.iter().map(|x| *x as usize) {
        for m in range.iter().map(|x| *x as usize) {
            for k in range.iter().map(|x| *x as usize) {
                let id = format!("{},{},{}", n,m,k);
                group.bench_with_input(&id, &(n,m,k),
                |bench, &(n,m,k)| {
                    let mut rng = rand::thread_rng();
                    let (G, H, U, g_0) = get_gens(n,m,k);
                    let a: Vec<_> = (0..(n*m)).map(|_| Scalar::random(&mut rng)).collect();
                    let b: Vec<_> = (0..(m*k)).map(|_| Scalar::random(&mut rng)).collect();
                    let c = tp_mat_mult(&a, &b, n, k);
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
                        n,
                        m,
                        k
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
                            n,
                            m,
                            k
                        ).is_ok());
                    });
                });
            }
        }
        
    }
    group.finish();

}

criterion_group!(folding_prove, prove_square_folding);

criterion_group!(folding_verify, verify_square_folding);

criterion_main!(folding_prove, folding_verify);