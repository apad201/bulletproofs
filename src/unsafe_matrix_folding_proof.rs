#![allow(non_snake_case)]
#![allow(dead_code)]
#![cfg_attr(feature = "docs", doc(include = "../docs/inner-product-protocol.md"))]
extern crate alloc;

use alloc::vec::Vec;

use core::iter;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::transcript::TranscriptProtocol;

#[derive(Clone, Debug)]
pub struct UnsafeMatrixFoldingProof {
    pub(crate) L_vec1: Vec<CompressedRistretto>,
    pub(crate) R_vec1: Vec<CompressedRistretto>,
    pub(crate) L_vec3: Vec<CompressedRistretto>,
    pub(crate) R_vec3: Vec<CompressedRistretto>,
    pub(crate) L_vec2: Vec<CompressedRistretto>,
    pub(crate) R_vec2: Vec<CompressedRistretto>,
    pub(crate) a: Scalar,
    pub(crate) b: Scalar,

    // These are for debugging purposes only, will be removed lated
    /* pub(crate) TESTx: Vec<Scalar>,
    pub(crate) TESTGf: RistrettoPoint,
    pub(crate) TESTHf: RistrettoPoint,
    pub(crate) TESTUf: RistrettoPoint, */
}

impl UnsafeMatrixFoldingProof {
    /// Create a matrix folding proof.
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The dimnsions of the matrices must all be powers of 2
    pub fn create(
        transcript: &mut Transcript,
        mut G_vec: Vec<RistrettoPoint>, // say these are stored in row-major
        mut H_vec: Vec<RistrettoPoint>,
        mut U_vec: Vec<RistrettoPoint>, // this used to be Q and was not a vector nor mutable
        mut a_vec: Vec<Scalar>,
        mut b_vec: Vec<Scalar>, // I WILL ASSUME b CONTAINS THE TRANSPOSE OF THE MATRIX B!!!!
        mut c_vec: Vec<Scalar>,
        mut n: usize, //not sure if these need to be mutable but I'm assuming yes
        mut m: usize,
        mut k: usize
    ) -> UnsafeMatrixFoldingProof {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut U = &mut U_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];
        let mut c = &mut c_vec[..];


        let one = Scalar::one();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n*m);
        assert_eq!(H.len(), m*k);
        assert_eq!(U.len(), n*k);
        assert_eq!(a.len(), n*m);
        assert_eq!(b.len(), m*k);
        assert_eq!(c.len(), n*k);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());
        assert!(m.is_power_of_two());
        assert!(k.is_power_of_two());

        // begin the transcript
        transcript.matrixfolding_domain_sep(n as u64, m as u64, k as u64); 

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let lg_m = m.next_power_of_two().trailing_zeros() as usize; 
        let lg_k = k.next_power_of_two().trailing_zeros() as usize;
        
        // create vectors for L and R values
        // 1 vecs are for folding A and C, 3 vecs for folding B and C, 2 vecs for folding A and B
        // will be used in order 1 -> 3 -> 2 to avoid taking transposes
        let mut L_vec1 = Vec::with_capacity(lg_n);
        let mut R_vec1 = Vec::with_capacity(lg_n);
        let mut L_vec3 = Vec::with_capacity(lg_k);
        let mut R_vec3 = Vec::with_capacity(lg_k);
        let mut L_vec2 = Vec::with_capacity(lg_m);
        let mut R_vec2 = Vec::with_capacity(lg_m);

        // Debugging: store challenges explicitly so we can check to be sure challenges
        // are recovered properly in verification.
        // Obviously this will NOT be part of the actual protocol
        // let mut TESTchall = Vec::with_capacity(lg_n + lg_m + lg_k);

        // first fold A vertically
        while n != 1 {
            // fold A and G vertically
            n = n/2;
            let (a_t, a_b) = a.split_at_mut(n*m);
            let (c_t, c_b) = c.split_at_mut(n*k);
            let (G_t, G_b) = G.split_at_mut(n*m);
            let (U_t, U_b) = U.split_at_mut(n*k);

            // compute L and R
            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_t.iter().chain(c_t.iter()), 
                G_b.iter().chain(U_b.iter())
            ).compress();

            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_b.iter().chain(c_b.iter()),
                G_t.iter().chain(U_t.iter())
            ).compress();

            // add L R to records for return struct
            L_vec1.push(L);
            R_vec1.push(R);

            // add L R to transcript
            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);      

            // get challenge and its inverse
            let x = transcript.challenge_scalar(b"x");
            let x_inv = x.invert();
            // for debugging: add challenge to record
            // TESTchall.push(x);
            // compute a', G'
            for i in 0..(n*m) {
                a_t[i] = x * a_t[i] + a_b[i];
                G_t[i] = RistrettoPoint::vartime_multiscalar_mul(&[x_inv, one], &[G_t[i], G_b[i]]);
            }

            // compute c', U'
            for i in 0..(n*k) {
                c_t[i] = x * c_t[i] + c_b[i];
                U_t[i] = RistrettoPoint::vartime_multiscalar_mul(&[x_inv, one], &[U_t[i], U_b[i]]);
            }

            // update a, c, G, U
            a = a_t;
            c = c_t;
            G = G_t;
            U = U_t;
        }


        // now fold B horizontally (i.e. fold b, which stores B^T, vertically)
        // Technically we need to find transpose of C (since it must also be folded horizontally), 
        // but since A is now a row vector, C is a row vector, so we can just
        // "re-interpret" it as a column vector and no actual work is needed to transpose it! which is very nice
        // confirm that n=1 by this point:
        // assert_eq!(n,1);
        while k != 1 {
            k = k/2;
            let (b_l, b_r) = b.split_at_mut(m*k);
            let (c_l, c_r) = c.split_at_mut(k); // n == 1 by the time we get here
            let (H_l, H_r) = H.split_at_mut(m*k);
            let (U_l, U_r) = U.split_at_mut(k);

            // compute L and R
            let L = RistrettoPoint::vartime_multiscalar_mul(
                b_l.iter().chain(c_l.iter()), 
                H_r.iter().chain(U_r.iter())
            ).compress();

            let R = RistrettoPoint::vartime_multiscalar_mul(
                b_r.iter().chain(c_r.iter()),
                H_l.iter().chain(U_l.iter())
            ).compress();

            // add L R to records for return struct
            L_vec3.push(L);
            R_vec3.push(R);

            // add L R to transcript
            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);      

            // get challenge and its inverse
            let x = transcript.challenge_scalar(b"x");
            let x_inv = x.invert();
            // TESTchall.push(x);

            // compute new b', H', c', U'
            for i in 0..(m*k) {
                b_l[i] = x * b_l[i] + b_r[i];
                H_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[x_inv, one], &[H_l[i], H_r[i]]);
            }

            for i in 0..k {
                c_l[i] = x * c_l[i] + c_r[i];
                U_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[x_inv, one], &[U_l[i], U_r[i]]);
            }

            b = b_l;
            H = H_l;
            c = c_l;
            U = U_l;
        }
     
        // now a is 1 x m and b is m x 1 and c is 1 x 1. 
        // because b stores B^T, which is a row vector, which we can reinterpret as the column vector B! yay
        // at this point it is just an inner product proof
        // to confirm that folding in other dimensions is done:
        /* assert_eq!(k,1);
        assert_eq!(n,1);
        assert_eq!(U.len(),1); */
        while m != 1 {
            m = m/2;
            let (a_l, a_r) = a.split_at_mut(m);
            let (b_t, b_b) = b.split_at_mut(m);
            let (G_l, G_r) = G.split_at_mut(m);
            let (H_t, H_b) = H.split_at_mut(m);

            // this time we need values of cross terms for L and R
            let c_l = inner_product(a_l, b_b);
            let c_r = inner_product(a_r, b_t);

            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_l.iter().chain(b_b.iter().chain(iter::once(&c_l))), 
                G_r.iter().chain(H_t.iter().chain(U.iter()))
            ).compress(); // at this point U should have length 1

            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_r.iter().chain(b_t.iter().chain(iter::once(&c_r))), 
                G_l.iter().chain(H_b.iter().chain(U.iter()))
            ).compress();

             // add L R to records for return struct
             L_vec2.push(L);
             R_vec2.push(R);
 
             // add L R to transcript
             transcript.append_point(b"L", &L);
             transcript.append_point(b"R", &R);  

             // get challenge and its inverse
            let x = transcript.challenge_scalar(b"x");
            let x_inv = x.invert();
            // TESTchall.push(x);

            for i in 0..m {
                a_l[i] = x * a_l[i] + a_r[i];
                b_t[i] = x_inv * b_t[i] + b_b[i];
                G_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[x_inv, one], &[G_l[i], G_r[i]]);
                H_t[i] = RistrettoPoint::vartime_multiscalar_mul(&[x, one], &[H_t[i], H_b[i]]);
            }

            a = a_l;
            b = b_t;
            G = G_l;
            H = H_t;

        }
        // return value
        // note proof keeps its own record of L and R terms from each iteration, separate from transcript
        UnsafeMatrixFoldingProof {
            L_vec1: L_vec1,
            R_vec1: R_vec1,
            L_vec3: L_vec3,
            R_vec3: R_vec3,
            L_vec2: L_vec2,
            R_vec2: R_vec2,
            a: a[0],
            b: b[0],

            // fields below will be removed, for debugging only
            /* TESTx: TESTchall,
            TESTGf: G[0],
            TESTHf: H[0],
            TESTUf: U[0] */
        }
    }

    /// Computes three vectors of verification scalars \\([u\_{i}^{2}]\\), \\([u\_{i}^{-2}]\\) and \\([s\_{i}]\\) for combined multiscalar multiplication
    /// in a parent protocol. See [inner product protocol notes](index.html#verification-equation) for details.
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation within the inner product proof.
    /// 
    /// added note from Aram: the linked page above is actually useful: https://doc-internal.dalek.rs/bulletproofs/inner_product_proof/index.html
    /// note everything is written additively here, so products become sums and exponentiations become products
    /// this verification equation matches the equation at the top of page 17 in the paper; s is the same as in the paper, but the u terms here are x terms in the paper
    /// 
    /// this method doesn't look like  it actually does any verification; it just returns the scalars needed for the verifier to do the verificatoin themselves
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        m: usize,
        k: usize,
        transcript: &mut Transcript,
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), ProofError> {
        let lg_n = self.L_vec1.len();
        let lg_m = self.L_vec2.len();
        let lg_k = self.L_vec3.len();

        let num_rounds = lg_n + lg_m + lg_k;
        if num_rounds >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.matrixfolding_domain_sep(n as u64, m as u64, k as u64);

        // 1. Recompute challenges based on the proof transcript

        let mut challenges1 = Vec::with_capacity(lg_n);
        let mut challenges3 = Vec::with_capacity(lg_k);
        let mut challenges2 = Vec::with_capacity(lg_m);

        for (L, R) in self.L_vec1.iter().zip(self.R_vec1.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges1.push(transcript.challenge_scalar(b"x"));
        }
        for (L, R) in self.L_vec3.iter().zip(self.R_vec3.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges3.push(transcript.challenge_scalar(b"x"));
        }
        for (L, R) in self.L_vec2.iter().zip(self.R_vec2.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges2.push(transcript.challenge_scalar(b"x"));
        }

        // Some debugging tests: ensure that challenges were correctly recovered
        /* let mut TESTchall = challenges1.clone();
        TESTchall.extend(&challenges3);
        TESTchall.extend(&challenges2);
        assert_eq!(TESTchall, self.TESTx); */

        // Need various mixes of challenges & their inverses to begin computing s-vectors
        let mut challenges1_inv = challenges1.clone();
        let allinv1 = Scalar::batch_invert(&mut challenges1_inv);
        let mut challenges2_inv = challenges2.clone();
        let allinv2 = Scalar::batch_invert(&mut challenges2_inv);
        let mut challenges3_inv = challenges3.clone();
        let allinv3 = Scalar::batch_invert(&mut challenges3_inv);
        let mut all2 = Scalar::one();
        for x in challenges2.iter() {
            all2 *= x;
        }

        let mut challengesG = challenges1.clone();
        challengesG.extend(&challenges2);
        let mut challengesH = challenges3.clone();
        challengesH.extend(&challenges2_inv);
        let mut challengesU = challenges1.clone();
        challengesU.extend(&challenges3);

        let s_G0 = allinv1 * allinv2;
        let s_H0 = allinv3 * all2;
        let s_U0 = allinv1 * allinv3;

        // all the copying above might be unnecessary. this definitely will hurt performance
        // is there a way to replace with chained iterators? don't think so but that would 
        // be nice

        // Compute s values inductively.
        let mut s_G = Vec::with_capacity(n*m);
        let mut s_H = Vec::with_capacity(m*k);
        let mut s_U = Vec::with_capacity(n*k);

        // compute G scalars (I think this code works fine just ripped straight from original)
        s_G.push(s_G0);
        for i in 1..(n*m) {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << lg_i; 
            let x_lg_i = challengesG[(lg_n + lg_m - 1) - lg_i];
            s_G.push(s_G[i - b] * x_lg_i);
        }

        s_H.push(s_H0);
        for i in 1..(m*k) {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << lg_i; 
            let x_lg_i = challengesH[(lg_m + lg_k - 1) - lg_i];
            s_H.push(s_H[i - b] * x_lg_i);
        }

        s_U.push(s_U0); 
        for i in 1..(n*k) {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << lg_i;
            let x_lg_i = challengesU[(lg_n + lg_k - 1) - lg_i];
            s_U.push(s_U[i - b] * x_lg_i);
        }
        //assert_eq!(s_G[n*m - 1], Scalar::one());
        //assert_eq!(s_G[0], challenges1_inv[0]);
        Ok((challenges1, challenges3, challenges2, challenges1_inv, challenges3_inv, challenges2_inv, s_G, s_H, s_U))
    }

    /// This method is for testing that proof generation works,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        P: &RistrettoPoint,
        G: &[RistrettoPoint],
        H: &[RistrettoPoint],
        U: &[RistrettoPoint],
        n: usize,
        m: usize,
        k: usize
    ) -> Result<(), ProofError> {
        // get verification scalars
        let (x1, x3, x2, x1_inv, x3_inv, x2_inv, s_G, s_H, s_U) = self.verification_scalars(n, m, k, transcript)?;

        // Debugging tests: confirms that all of the s-vectors were computed correctly.
        // Also guarantees that folded G, H, and U group elements were computed correctly
        // during proof generation
        /* let TESTG = RistrettoPoint::vartime_multiscalar_mul(s_G.iter(), G.iter());
        assert_eq!(TESTG, self.TESTGf);
        let TESTH = RistrettoPoint::vartime_multiscalar_mul(s_H.iter(), H.iter());
        assert_eq!(TESTH, self.TESTHf);
        let TESTU = RistrettoPoint::vartime_multiscalar_mul(s_U.iter(), U.iter());
        assert_eq!(TESTU, self.TESTUf); */

        // compute remaining exponents for verification equation (for G and H and U terms)
        let g_exp = s_G.iter().map(|s_i| self.a * s_i);
        let h_exp = s_H.iter().map(|s_i| self.b * s_i);
        let c = self.a * self.b;
        let u_exp = s_U.iter().map(|s_i| c * s_i);

        // Debugging tests: ensures above computations worked as expected
        /* let H_EXPED = RistrettoPoint::vartime_multiscalar_mul(h_exp.clone(), H.iter());
        let Hf_EXPED = RistrettoPoint::vartime_multiscalar_mul(iter::once(&self.b), iter::once(self.TESTHf));
        assert_eq!(H_EXPED, Hf_EXPED); */

        // Compute more verification exponents (here for L and R terms)
        let neg_x = x1.iter()
            .chain(x3.iter())
            .chain(x2.iter())
            .map(|xi| -xi);
        let neg_x_inv = x1_inv.iter()
            .chain(x3_inv.iter())
            .chain(x2_inv.iter())
            .map(|xi| -xi);

        // Debugging tests: confirm L and R exponents agree with outputs from verification_scalars fn
        /* for (val1, val2) in neg_x.clone().zip(neg_x_inv.clone()) {
            assert_eq!(val1 * val2, Scalar::one());
        }
        for (val1, val2) in neg_x.clone().zip(x1.iter().chain(x3.iter().chain(x2.iter()))) {
            assert_eq!(val1 + val2, Scalar::zero());
        } */

        // Get L and R values from proof
        let Ls = self
            .L_vec1
            .iter()
            .chain(self.L_vec3
            .iter()
            .chain(self.L_vec2
            .iter()))
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = self
            .R_vec1
            .iter()
            .chain(self.R_vec3
            .iter()
            .chain(self.R_vec2
            .iter()))
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        // Compute the verification eqn
        let expect_P = RistrettoPoint::vartime_multiscalar_mul(
            g_exp
                .chain(h_exp)
                .chain(u_exp)
                .chain(neg_x)
                .chain(neg_x_inv),
            G.iter()
                .chain(H.iter())
                .chain(U.iter())
                .chain(Ls.iter())
                .chain(Rs.iter())
        );

        // See if verification passes
        if expect_P == *P {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }
}

// This assumes a is row-major, b is a row-major representation of b TRANSPOSE
// so we want to calculate a*b, but we are given the transpose of b as input
// a should have n rows and b should have k columns (so b transpose should have k rows)
pub fn mat_mult(a: &[Scalar], b: &[Scalar], n: usize, k: usize) -> Vec<Scalar> {
    let mut c = Vec::with_capacity(n*k);
    let m = a.len()/n;
    // assert_eq!(m, b.len()/k);
    for a_row in a.chunks(m) {
        for b_col in b.chunks(m) {
            c.push(inner_product(a_row,b_col));
        }
    }
    c
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

// below are the debugging tests
#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;



    fn mfp_test_helper_create(n: usize, m: usize, k: usize) {
        let mut rng = rand::thread_rng();

        // get group elements. See generators.rs file for how this works; I basically copied
        // the way the bp_gens worked and just added more for U and removed the aggregation
        // since we aren't working with that
        use crate::generators::MatrixFoldingGens;
        let mf_gens = MatrixFoldingGens::new(n, m, k);
        let G: Vec<RistrettoPoint> = mf_gens.G();
        let H: Vec<RistrettoPoint> = mf_gens.H();
        let U: Vec<RistrettoPoint> = mf_gens.U();

        // a and b are the matrices for which we want to prove c=ab
        // just generate random matrices every time
        let a: Vec<_> = (0..(n*m)).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..(m*k)).map(|_| Scalar::random(&mut rng)).collect();
        let c = mat_mult(&a, &b, n, k);

        // debugging check: be sure matrix multiplication matches inner product if applicable
        /* if n == 1 && k == 1 {
           assert_eq!(c[0], inner_product(&a, &b));
        } */

        // Compute commitment P
        let P = RistrettoPoint::vartime_multiscalar_mul(
            a.iter()
                .chain(b.iter())
                .chain(c.iter()),
            G.iter()
                .chain(H.iter())
                .chain(U.iter())
        );

        // generate proof
        let mut prover = Transcript::new(b"matrixfoldingtest");
        let proof = UnsafeMatrixFoldingProof::create(
            &mut prover,
            G.clone(),
            H.clone(),
            U.clone(),
            a.clone(),
            b.clone(),
            c.clone(),
            n,
            m,
            k
        );

        // verify proof
        let mut verifier = Transcript::new(b"matrixfoldingtest");
        assert!(proof.verify(
            &mut verifier,
            &P,
            &G[..],
            &H[..],
            &U[..],
            n,
            m,
            k
        )
            .is_ok());
    }

    // test cases: currently tests 1-5 pass and 6-9 fail (fails whenever m \neq 1)
    #[test]
    fn u_make_mfp_1() {
        mfp_test_helper_create(1, 1, 1);
    }

    #[test]
    fn u_make_mfp_2() {
        mfp_test_helper_create(16, 1, 1);
    }

    #[test]
    fn u_make_mfp_3() {
        mfp_test_helper_create(1,1,16);
    }

    #[test]
    fn u_make_mfp_4() {
        mfp_test_helper_create(16,1,16);
    }

    #[test]
    fn u_make_mfp_5() {
        mfp_test_helper_create(16,1,32);
    }

    #[test]
    fn u_make_mfp_6() {
        mfp_test_helper_create(1,16,1);
    }

    #[test]
    fn u_make_mfp_7() {
        mfp_test_helper_create(8,16,1);
    }

    #[test]
    fn u_make_mfp_8() {
        mfp_test_helper_create(1,16,8);
    }

    #[test]
    fn u_make_mfp_9() {
        mfp_test_helper_create(32,4,8);
    }

    #[test]
    fn make_mfp_time_1() {
        mfp_test_helper_create(1024,2048,512);
    }

    fn mat_mult_test_helper(n: usize, m: usize, k: usize) {
        let mut rng = rand::thread_rng();
        let a: Vec<_> = (0..(n*m)).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..(m*k)).map(|_| Scalar::random(&mut rng)).collect();
        let c = mat_mult(&a, &b, n, k);
        
        for x in 0..n {
            for y in 0..k {
                assert_eq!(inner_product(&a[x*m..(x+1)*m], &b[y*m..(y+1)*m]), c[k*x + y]);
            }
        }
    }

    #[test]
    fn mm_test_1() {
        mat_mult_test_helper(1, 1, 1);
    }

    #[test]
    fn mm_test_2() {
        mat_mult_test_helper(16,1,1);
    }

    #[test]
    fn mm_test_3() {
        mat_mult_test_helper(1,1,16);
    }

    #[test]
    fn mm_test_4() {
        mat_mult_test_helper(16,1,16);
    }

    #[test]
    fn mm_test_5() {
        mat_mult_test_helper(1,16,1);
    }

    #[test]
    fn mm_test_6() {
        mat_mult_test_helper(16,32,1);
    }

    #[test]
    fn mm_test_7() {
        mat_mult_test_helper(1,32,16);
    }

    #[test]
    fn mm_test_8() {
        mat_mult_test_helper(64,32,16);
    }

    #[test]
    fn mm_test_9() {
        mat_mult_test_helper(2,2,2);
    }


    fn mfp_timing_setup(n: usize, m: usize, k: usize) -> (Vec<RistrettoPoint>, Vec<RistrettoPoint>, Vec<RistrettoPoint>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
        let mut rng = rand::thread_rng();

        // get group elements. See generators.rs file for how this works; I basically copied
        // the way the bp_gens worked and just added more for U and removed the aggregation
        // since we aren't working with that
        use crate::generators::MatrixFoldingGens;
        let mf_gens = MatrixFoldingGens::new(n, m, k);
        let G: Vec<RistrettoPoint> = mf_gens.G();
        let H: Vec<RistrettoPoint> = mf_gens.H();
        let U: Vec<RistrettoPoint> = mf_gens.U();

        // a and b are the matrices for which we want to prove c=ab
        // just generate random matrices every time
        let a: Vec<_> = (0..(n*m)).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..(m*k)).map(|_| Scalar::random(&mut rng)).collect();
        let c = mat_mult(&a, &b, n, k);
        (G, H, U, a, b, c)
    }

    fn mfp_timing_helper(n: usize, m: usize, k: usize) {
        let setup_start = Instant::now();
        let (G, H, U, a, b, c) = mfp_timing_setup(n, m, k);
        let setup_duration = setup_start.elapsed();
        // generate proof
        let mut prover = Transcript::new(b"matrixfoldingtest");
        let create_start = Instant::now();
        let proof = UnsafeMatrixFoldingProof::create(
            &mut prover,
            G.clone(),
            H.clone(),
            U.clone(),
            a.clone(),
            b.clone(),
            c.clone(),
            n,
            m,
            k
        );
        let create_duration = create_start.elapsed();

        let P = RistrettoPoint::vartime_multiscalar_mul(
            a.iter()
                .chain(b.iter())
                .chain(c.iter()),
            G.iter()
                .chain(H.iter())
                .chain(U.iter())
        );

        let mut verifier = Transcript::new(b"matrixfoldingtest");
        let verify_start = Instant::now();
        assert!(proof.verify(
            &mut verifier,
            &P,
            &G[..],
            &H[..],
            &U[..],
            n,
            m,
            k
        )
            .is_ok());
        let verify_duration = verify_start.elapsed();

        println!("SIZE n={}, m={}, k={}. DURATION setup={}, create={}, verify={}", 
                n, m, k, 
                setup_duration.as_secs_f32(),
                create_duration.as_secs_f32(),
                verify_duration.as_secs_f32()
                );
    }

    #[test]
    fn mfp_timing_1() {
        mfp_timing_helper(1, 1, 1);
    }

    #[test]
    fn mfp_timing_2() {
        mfp_timing_helper(2, 1, 1);
    }

    #[test]
    fn mfp_timing_3() {
        mfp_timing_helper(4, 1, 1);
    }

    #[test]
    fn mfp_timing_4() {
        mfp_timing_helper(8, 1, 1);
    }

    #[test]
    fn mfp_timing_5() {
        mfp_timing_helper(32, 32, 32);
    }

    #[test]
    fn mfp_timing_6() {
        mfp_timing_helper(64, 64, 64);
    }

    #[test]
    fn mfp_timing_7() {
        mfp_timing_helper(128, 256, 512);
    }

}

