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
pub struct ZKMatrixFoldingProof {
    pub(crate) L_vec1: Vec<CompressedRistretto>,
    pub(crate) R_vec1: Vec<CompressedRistretto>,
    pub(crate) L_vec2: Vec<CompressedRistretto>,
    pub(crate) R_vec2: Vec<CompressedRistretto>,
    pub(crate) L_vec3_beta: Vec<CompressedRistretto>,
    pub(crate) R_vec3_beta: Vec<CompressedRistretto>,
    pub(crate) L_vec3_tau: Vec<CompressedRistretto>,
    pub(crate) R_vec3_tau: Vec<CompressedRistretto>,
    pub(crate) alpha: CompressedRistretto,
    pub(crate) beta: CompressedRistretto,
    pub(crate) sigma: CompressedRistretto,
    pub(crate) tau: CompressedRistretto,
    pub(crate) rho_vec: Vec<CompressedRistretto>,
    pub(crate) z_vec: Vec<Scalar>,
}

impl ZKMatrixFoldingProof {
    // Create a matrix folding proof.
    pub fn create(
        transcript: &mut Transcript,
        public_parameters: (
            Vec<RistrettoPoint>,
            Vec<RistrettoPoint>,
            Vec<RistrettoPoint>,
            RistrettoPoint,
        ), // blinding group element
        witness: (
            Vec<Scalar>,
            Vec<Scalar>, // row-major
            Scalar,
        ), // blinding exponent
        dim: (usize, usize, usize),
    ) -> ZKMatrixFoldingProof {
        // Create slices G, H, a, b backed by their respective
        // vectors. This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut dim_n = dim.0;
        let mut dim_m = dim.1;
        let mut dim_k = dim.2;

        let mut witness_a = witness.0;
        let mut witness_b = witness.1;
        let mut blinding_r = witness.2;

        let mut public_G = public_parameters.0;
        let mut public_H = public_parameters.1;
        let mut public_U = public_parameters.2;
        let g_0 = public_parameters.3;

        let mut public_G = &mut public_G[..];
        let mut public_H = &mut public_H[..];
        let mut public_U = &mut public_U[..];
        let mut witness_a = &mut witness_a[..];
        let mut witness_b = &mut witness_b[..];

        let one = Scalar::one();

        // for generating random blinding factors
        let mut rng = rand::thread_rng();

        // All of the input vectors must have the correct length
        assert_eq!(public_G.len(), dim_n * dim_m);
        assert_eq!(public_H.len(), dim_m * dim_k);
        assert_eq!(public_U.len(), dim_n * dim_k);
        assert_eq!(witness_a.len(), dim_n * dim_m);
        assert_eq!(witness_b.len(), dim_m * dim_k);

        // All of the dimensions of matrices must be a power of two.
        assert!(dim_n.is_power_of_two());
        assert!(dim_m.is_power_of_two());
        assert!(dim_k.is_power_of_two());

        // begin the transcript
        transcript.matrixfolding_domain_sep(dim_n as u64, dim_m as u64, dim_k as u64);

        let log_n = dim_n.next_power_of_two().trailing_zeros() as usize;
        let log_m = dim_m.next_power_of_two().trailing_zeros() as usize;
        let log_k = dim_k.next_power_of_two().trailing_zeros() as usize;

        // create vectors for L and R values
        let mut L_vec1 = Vec::with_capacity(log_m);

        let mut R_vec1 = Vec::with_capacity(log_m);
        let mut L_vec2 = Vec::with_capacity(log_n);
        let mut R_vec2 = Vec::with_capacity(log_n);
        let mut L_vec3_beta = Vec::with_capacity(log_k);
        let mut R_vec3_beta = Vec::with_capacity(log_k);
        let mut L_vec3_tau = Vec::with_capacity(log_k);
        let mut R_vec3_tau = Vec::with_capacity(log_k);

        // first fold A and B with inner product approach
        // A must be coloumn-major so that splitting in half correctly splits the matrix down the middle
        while dim_m != 1 {
            dim_m /= 2;
            let (witness_a_left, witness_a_right) = witness_a.split_at_mut(dim_m * dim_n);
            let (b_t, b_b) = witness_b.split_at_mut(dim_m * dim_k);
            let (G_l, G_r) = public_G.split_at_mut(dim_m * dim_n);
            let (H_t, H_b) = public_H.split_at_mut(dim_m * dim_k);

            // get cross terms for L and R
            // these are matrix multiplications :(
            let c_l = tp_mat_mult(witness_a_left, b_b, dim_n, dim_k);
            let c_r = tp_mat_mult(witness_a_right, b_t, dim_n, dim_k);

            // gemerate blinding factors for L and R
            let blinding_r_left = Scalar::random(&mut rng);
            let blinding_r_right = Scalar::random(&mut rng);

            // compute L and R
            let L = RistrettoPoint::vartime_multiscalar_mul(
                witness_a_left
                    .iter()
                    .chain(b_b.iter())
                    .chain(c_l.iter())
                    .chain(iter::once(&blinding_r_left)),
                G_r.iter()
                    .chain(H_t.iter())
                    .chain(public_U.iter())
                    .chain(iter::once(&g_0)),
            )
            .compress();

            let R = RistrettoPoint::vartime_multiscalar_mul(
                witness_a_right
                    .iter()
                    .chain(b_t.iter())
                    .chain(c_r.iter())
                    .chain(iter::once(&blinding_r_right)),
                G_l.iter()
                    .chain(H_b.iter())
                    .chain(public_U.iter())
                    .chain(iter::once(&g_0)),
            )
            .compress();

            // add L and R to records for return struct
            L_vec1.push(L);
            R_vec1.push(R);

            // add L and R to transcript
            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            // get challenge and its inverse
            let x = transcript.challenge_scalar(b"x");
            let x_inv = x.invert();

            for i in 0..(dim_n * dim_m) {
                witness_a_left[i] = x * witness_a_left[i] + witness_a_right[i];
                G_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[x_inv, one], &[G_l[i], G_r[i]]);
            }
            //Now, zip, map do this.

            for i in 0..(dim_m * dim_k) {
                b_t[i] = x_inv * b_t[i] + b_b[i];
                H_t[i] = RistrettoPoint::vartime_multiscalar_mul(&[x, one], &[H_t[i], H_b[i]]);
            }

            blinding_r = (x * blinding_r_left) + blinding_r + (x_inv * blinding_r_right);
            witness_a = witness_a_left;
            witness_b = b_t;
            public_G = G_l;
            public_H = H_t;
        }

        // now for "mini-reduction" 1, to transform the commitments
        //TODO current
        //CURRENT1

        let mut c_vec = tp_mat_mult(witness_a, witness_b, dim_n, dim_k);
        let mut c = &mut c_vec[..];

        //let mut q: Scalar;
        let (alpha, beta, blinding_r, q) = reduction_lambda_1(
            (public_G, public_H, public_U, g_0),
            (witness_a, witness_b, c, blinding_r),
        );

        let mut q = q; //TODO: stupid line
        let mut blinding_r = blinding_r;

        transcript.append_point(b"a", &alpha);
        transcript.append_point(b"b", &beta);

        // Now, fold n (A)
        // A now holds a col vector, so can fold vertically easily
        while dim_n != 1 {
            dim_n /= 2;
            let (a_t, a_b) = witness_a.split_at_mut(dim_n);
            let (c_t, c_b) = c.split_at_mut(dim_n * dim_k);
            let (G_t, G_b) = public_G.split_at_mut(dim_n);
            let (U_t, U_b) = public_U.split_at_mut(dim_n * dim_k);

            // gemerate blinding factors for L and R
            let q_l = Scalar::random(&mut rng);
            let q_r = Scalar::random(&mut rng);

            // compute L and R
            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_t.iter().chain(c_t.iter()).chain(iter::once(&q_l)),
                G_b.iter().chain(U_b.iter()).chain(iter::once(&g_0)),
            )
            .compress();

            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_b.iter().chain(c_b.iter()).chain(iter::once(&q_r)),
                G_t.iter().chain(U_t.iter()).chain(iter::once(&g_0)),
            )
            .compress();

            // add L R to records for return struct
            L_vec2.push(L);
            R_vec2.push(R);

            // add L R to transcript
            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            // get challenge and its inverse
            let y = transcript.challenge_scalar(b"y");
            let y_inv = y.invert();

            // compute new a, G
            for i in 0..dim_n {
                a_t[i] = y * a_t[i] + a_b[i];
                G_t[i] = RistrettoPoint::vartime_multiscalar_mul(&[y_inv, one], &[G_t[i], G_b[i]]);
            }

            // compute new c, U
            for i in 0..(dim_n * dim_k) {
                c_t[i] = y * c_t[i] + c_b[i];
                U_t[i] = RistrettoPoint::vartime_multiscalar_mul(&[y_inv, one], &[U_t[i], U_b[i]]);
            }

            // compute and update q
            q = (y * q_l) + q + (y_inv * q_r);

            // update a, c, G, U
            witness_a = a_t;
            c = c_t;
            public_G = G_t;
            public_U = U_t;
        }

        //CURRENT2
        // mini-reduction 2: transform commitments again

        let (sigma, tau, q, s) = reduction_lambda_2((public_G, public_U, g_0), (witness_a, c, q));
        transcript.append_point(b"s", &sigma);
        transcript.append_point(b"t", &tau);

        //TODO: stupid lines
        let q = q;
        let mut s = s;
        //CURRENT2

        // now fold k/B
        while dim_k != 1 {
            dim_k /= 2;
            let (b_l, b_r) = witness_b.split_at_mut(dim_k);
            let (c_l, c_r) = c.split_at_mut(dim_k); // n == 1 by the time we get here
            let (H_l, H_r) = public_H.split_at_mut(dim_k);
            let (U_l, U_r) = public_U.split_at_mut(dim_k);

            // blinding
            let blinding_r_left = Scalar::random(&mut rng);
            let blinding_r_right = Scalar::random(&mut rng);
            let s_l = Scalar::random(&mut rng);
            let s_r = Scalar::random(&mut rng);

            // commitments: note we have 4 here, since we need 2 for beta and 2 for tau
            let L_beta = RistrettoPoint::vartime_multiscalar_mul(
                b_l.iter().chain(iter::once(&blinding_r_left)),
                H_r.iter().chain(iter::once(&g_0)),
            )
            .compress();

            let R_beta = RistrettoPoint::vartime_multiscalar_mul(
                b_r.iter().chain(iter::once(&blinding_r_right)),
                H_l.iter().chain(iter::once(&g_0)),
            )
            .compress();

            let L_tau = RistrettoPoint::vartime_multiscalar_mul(
                c_l.iter().chain(iter::once(&s_l)),
                U_r.iter().chain(iter::once(&g_0)),
            )
            .compress();

            let R_tau = RistrettoPoint::vartime_multiscalar_mul(
                c_r.iter().chain(iter::once(&s_r)),
                U_l.iter().chain(iter::once(&g_0)),
            )
            .compress();

            // store
            L_vec3_beta.push(L_beta);
            R_vec3_beta.push(R_beta);
            L_vec3_tau.push(L_tau);
            R_vec3_tau.push(R_tau);

            // add Ls and Rs to transcript
            transcript.append_point(b"bL", &L_beta);
            transcript.append_point(b"bR", &R_beta);
            transcript.append_point(b"tL", &L_tau);
            transcript.append_point(b"tR", &R_tau);

            // get challenge and its inverse
            let z = transcript.challenge_scalar(b"z");
            let z_inv = z.invert();

            // debug
            // TESTchall.push(z);

            // compute new b, H
            for i in 0..dim_k {
                b_l[i] = z * b_l[i] + b_r[i];
                H_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[z_inv, one], &[H_l[i], H_r[i]]);
            }

            // compute new c, U
            for i in 0..dim_k {
                // n == 1
                c_l[i] = z * c_l[i] + c_r[i];
                U_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[z_inv, one], &[U_l[i], U_r[i]]);
            }
            // compute + update blindings
            blinding_r = (z * blinding_r_left) + blinding_r + (z_inv * blinding_r_right);
            s = (z * s_l) + s + (z_inv * s_r);

            // update values
            witness_b = b_l;
            c = c_l;
            public_H = H_l;
            public_U = U_l;
        }

        // final ZK scalar mult step

        // compute blinding factors and commitments
        let t: Vec<_> = (0..5).map(|_| Scalar::random(&mut rng)).collect();
        let rho_0 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&t[0]).chain(iter::once(&t[1])),
            public_G.iter().chain(iter::once(&g_0)),
        )
        .compress();
        let rho_1 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&t[2]).chain(iter::once(&t[3])),
            public_H.iter().chain(iter::once(&g_0)),
        )
        .compress();
        let rho_2 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&(t[0] * t[2])).chain(iter::once(&t[4])),
            public_U.iter().chain(iter::once(&g_0)),
        )
        .compress();
        let rho_3 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&(t[0] * witness_b[0] + t[2] * witness_a[0])),
            public_U.iter(),
        )
        .compress();

        let rho_vec = vec![rho_0, rho_1, rho_2, rho_3];

        // add commitments to transcript
        for comm in rho_vec.iter() {
            transcript.append_point(b"rh", comm);
        }

        // get challenge
        let x = transcript.challenge_scalar(b"x");

        // compute responses
        let z_0 = t[0] + (witness_a[0] * x);
        let z_1 = t[1] + (q * x);
        let z_2 = t[2] + (witness_b[0] * x);
        let z_3 = t[3] + (blinding_r * x);
        let z_4 = t[4] + (s * x * x);

        let z_vec = vec![z_0, z_1, z_2, z_3, z_4];

        // package everything up into the struct to return, compressing as needed
        ZKMatrixFoldingProof {
            L_vec1,
            R_vec1,
            L_vec2,
            R_vec2,
            L_vec3_beta,
            R_vec3_beta,
            L_vec3_tau,
            R_vec3_tau,
            alpha,
            beta,
            sigma,
            tau,
            rho_vec,
            z_vec, // fields below will be removed, for debugging only
                   /* TESTx: TESTchall,
                   TESTGf: G[0],
                   TESTHf: H[0],
                   TESTUf: U[0]  */
        }
    }

    /// Computes verification scalars: the exponents of G, H and U used in verification to compute the final value of
    /// these public parameters given the initial public parameters and the challenges used throughout.
    /// works in a manner very similar to the original implementation in Bulletproofs
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        m: usize,
        k: usize,
        transcript: &mut Transcript,
    ) -> Result<
        (
            Vec<Scalar>,
            Vec<Scalar>,
            Vec<Scalar>,
            Vec<Scalar>,
            Vec<Scalar>,
            Vec<Scalar>,
            Scalar,
            Vec<Scalar>,
            Vec<Scalar>,
            Vec<Scalar>,
        ),
        ProofError,
    > {
        let log_m = self.L_vec1.len();
        let log_n = self.L_vec2.len();
        let log_k = self.L_vec3_beta.len();

        if log_n >= 32 || log_m >= 32 || log_k >= 32 {
            // prevent overflow in bitshifts later on
            return Err(ProofError::VerificationError);
        }
        if (log_n != 0 && n != (1 << log_n))
            || (log_m != 0 && m != (1 << log_m))
            || (log_k != 0 && k != (1 << log_k))
        {
            // not powers of 2
            return Err(ProofError::VerificationError);
        }
        if self.L_vec3_tau.len() != log_k
            || self.R_vec3_beta.len() != log_k
            || self.R_vec3_tau.len() != log_k
        {
            // malformed vectors
            return Err(ProofError::VerificationError);
        }

        //debug
        // println!("Verification_scalars passed first checks");

        transcript.matrixfolding_domain_sep(n as u64, m as u64, k as u64);

        // 1. Recompute challenges based on the proof transcript
        // add everything to transcript and get challenges, just like the Prover does

        let mut challenges1 = Vec::with_capacity(log_m);
        let mut challenges2 = Vec::with_capacity(log_n);
        let mut challenges3 = Vec::with_capacity(log_k);

        for (L, R) in self.L_vec1.iter().zip(self.R_vec1.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges1.push(transcript.challenge_scalar(b"x"));
        }

        transcript.validate_and_append_point(b"a", &self.alpha)?;
        transcript.validate_and_append_point(b"b", &self.beta)?;

        for (L, R) in self.L_vec2.iter().zip(self.R_vec2.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges2.push(transcript.challenge_scalar(b"y"));
        }

        transcript.validate_and_append_point(b"s", &self.sigma)?;
        transcript.validate_and_append_point(b"t", &self.tau)?;

        let iter3 = self
            .L_vec3_beta
            .iter()
            .zip(self.R_vec3_beta.iter())
            .zip(self.L_vec3_tau.iter())
            .zip(self.R_vec3_tau.iter())
            .map(|(((x, y), z), w)| (x, y, z, w));
        for (L_beta, R_beta, L_tau, R_tau) in iter3 {
            transcript.validate_and_append_point(b"bL", L_beta)?;
            transcript.validate_and_append_point(b"bR", &R_beta)?;
            transcript.validate_and_append_point(b"tL", L_tau)?;
            transcript.validate_and_append_point(b"tR", R_tau)?;
            challenges3.push(transcript.challenge_scalar(b"z"));
        }

        for comm in self.rho_vec.iter() {
            transcript.validate_and_append_point(b"rh", comm)?;
        }
        let zk_mult_chall = transcript.challenge_scalar(b"x");

        // Some debugging tests: ensure that challenges were correctly recovered
        /* let mut TESTchall = challenges1.clone();
        TESTchall.extend(&challenges2);
        TESTchall.extend(&challenges3);
        assert_eq!(TESTchall, self.TESTx);  */

        // Need various mixes of challenges & their inverses to begin computing verification scalars
        let mut challenges1_inv = challenges1.clone();
        let allinv1 = Scalar::batch_invert(&mut challenges1_inv);
        let mut challenges2_inv = challenges2.clone();
        let allinv2 = Scalar::batch_invert(&mut challenges2_inv);
        let mut challenges3_inv = challenges3.clone();
        let allinv3 = Scalar::batch_invert(&mut challenges3_inv);
        let mut all1 = Scalar::one();
        for y in challenges1.iter() {
            all1 *= y;
        }

        let mut challengesG = challenges1.clone();
        challengesG.extend(&challenges2);
        let mut challengesH = challenges1_inv.clone();
        challengesH.extend(&challenges3);
        let mut challengesU = challenges2.clone();
        challengesU.extend(&challenges3);

        let s_G0 = allinv1 * allinv2;
        let s_H0 = all1 * allinv3;
        let s_U0 = allinv2 * allinv3;

        // Compute s values inductively.
        let mut s_G = Vec::with_capacity(n * m);
        let mut s_H = Vec::with_capacity(m * k);
        let mut s_U = Vec::with_capacity(n * k);

        s_G.push(s_G0);
        for i in 1..(n * m) {
            let log_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << log_i;
            let x_log_i = challengesG[(log_n + log_m - 1) - log_i];
            s_G.push(s_G[i - b] * x_log_i);
        }

        s_H.push(s_H0);
        for i in 1..(m * k) {
            let log_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << log_i;
            let x_log_i = challengesH[(log_m + log_k - 1) - log_i];
            s_H.push(s_H[i - b] * x_log_i);
        }

        s_U.push(s_U0);
        for i in 1..(n * k) {
            let log_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << log_i;
            let x_log_i = challengesU[(log_n + log_k - 1) - log_i];
            s_U.push(s_U[i - b] * x_log_i);
        }

        Ok((
            challenges1,
            challenges2,
            challenges3,
            challenges1_inv,
            challenges2_inv,
            challenges3_inv,
            zk_mult_chall,
            s_G,
            s_H,
            s_U,
        ))
    }

    /// Perform verification
    #[allow(dead_code)]
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        P: &RistrettoPoint,
        G: &[RistrettoPoint],
        H: &[RistrettoPoint],
        U: &[RistrettoPoint],
        g_0: &RistrettoPoint,
        n: usize,
        m: usize,
        k: usize,
    ) -> Result<(), ProofError> {
        //debug
        // println!("BEGIN computations");

        let one = Scalar::one();
        let (x1, x2, x3, x1_inv, x2_inv, x3_inv, zk_mult_chall, s_G, s_H, s_U) =
            self.verification_scalars(n, m, k, transcript)?;

        // debug: check the verification scalars (exponents for G H U) were computed correctly
        /* let G_actual = RistrettoPoint::vartime_multiscalar_mul(s_G.iter(), G.iter());
        assert_eq!(G_actual, self.TESTGf);
        let H_actual = RistrettoPoint::vartime_multiscalar_mul(s_H.iter(), H.iter());
        assert_eq!(H_actual, self.TESTHf);
        let U_actual = RistrettoPoint::vartime_multiscalar_mul(s_U.iter(), U.iter());
        assert_eq!(U_actual, self.TESTUf); */

        // check for mini-reduction 1
        let alpha = self
            .alpha
            .decompress()
            .ok_or(ProofError::VerificationError)?;
        let beta = self
            .beta
            .decompress()
            .ok_or(ProofError::VerificationError)?;
        // need final value of P after done with Phi_1 (i.e., once m == 1)
        // so we need all the Ls and Rs
        let Ls = self
            .L_vec1
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let Rs = self
            .R_vec1
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let P_final = RistrettoPoint::vartime_multiscalar_mul(
            x1.iter().chain(x1_inv.iter()).chain(iter::once(&one)),
            Ls.iter().chain(Rs.iter()).chain(iter::once(P)),
        );
        // debug
        /* println!("MINI-RED 1 CHECK");
        assert_eq!(alpha + beta, P_final); */

        if alpha + beta != P_final {
            return Err(ProofError::VerificationError);
        }

        // check for mini-reduction 2
        let sigma = self
            .sigma
            .decompress()
            .ok_or(ProofError::VerificationError)?;
        let tau = self.tau.decompress().ok_or(ProofError::VerificationError)?;
        // need to compute value of alpha after all runs of reduction Phi2 (once n == 1)
        let alphwitness_a_lefts = self
            .L_vec2
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let alphwitness_a_rights = self
            .R_vec2
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let alpha_final = RistrettoPoint::vartime_multiscalar_mul(
            x2.iter().chain(x2_inv.iter()).chain(iter::once(&one)),
            alphwitness_a_lefts
                .iter()
                .chain(alphwitness_a_rights.iter())
                .chain(iter::once(&alpha)),
        );

        //debug
        // assert_eq!(sigma + beta + tau, alpha_final + beta);

        if sigma + beta + tau != alpha_final + beta {
            return Err(ProofError::VerificationError);
        }

        // check for mini-reduction 3
        // this one is different: still need the final values of beta and tau
        // but also need to get the other values used in the checks for mini-reduction 3
        let betwitness_a_lefts = self
            .L_vec3_beta
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let betwitness_a_rights = self
            .R_vec3_beta
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let beta_points = betwitness_a_lefts
            .iter()
            .chain(betwitness_a_rights.iter())
            .chain(iter::once(&beta));

        let tau_Ls = self
            .L_vec3_tau
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let tau_Rs = self
            .R_vec3_tau
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let tau_points = tau_Ls.iter().chain(tau_Rs.iter()).chain(iter::once(&tau));

        // compute remaining exponents for verification equation (for G and H and U terms)
        let g_exp = s_G.iter().map(|s_i| self.z_vec[0] * s_i);
        let h_exp = s_H.iter().map(|s_i| self.z_vec[2] * s_i);
        let c = self.z_vec[0] * self.z_vec[2];
        let u_exp = s_U.iter().map(|s_i| c * s_i);

        let neg_zk_mult_chall = -zk_mult_chall;
        let neg_zk_mult_chall_sq = zk_mult_chall * neg_zk_mult_chall;

        let beta_exp = x3
            .iter()
            .chain(x3_inv.iter())
            .chain(iter::once(&one))
            .map(|x| x * neg_zk_mult_chall);

        let tau_exp = x3
            .iter()
            .chain(x3_inv.iter())
            .chain(iter::once(&one))
            .map(|x| x * neg_zk_mult_chall_sq);

        // we will need the rho commitments
        let rho = self
            .rho_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        // first check of mini-red 3
        let check1 = RistrettoPoint::vartime_multiscalar_mul(
            g_exp
                .chain(iter::once(self.z_vec[1]))
                .chain(iter::once(neg_zk_mult_chall)),
            G.iter().chain(iter::once(g_0)).chain(iter::once(&sigma)),
        );

        //debug
        // assert_eq!(check1, rho[0]);

        if check1 != rho[0] {
            return Err(ProofError::VerificationError);
        }

        // second check of mini-red 3
        let check2 = RistrettoPoint::vartime_multiscalar_mul(
            h_exp.chain(iter::once(self.z_vec[3])).chain(beta_exp),
            H.iter().chain(iter::once(g_0)).chain(beta_points),
        );

        //debug
        // assert_eq!(check2, rho[1]);

        if check2 != rho[1] {
            return Err(ProofError::VerificationError);
        }

        // third check of mini-red 3
        let check3 = RistrettoPoint::vartime_multiscalar_mul(
            u_exp
                .chain(iter::once(self.z_vec[4]))
                .chain(iter::once(neg_zk_mult_chall))
                .chain(tau_exp),
            U.iter()
                .chain(iter::once(g_0))
                .chain(iter::once(&rho[3]))
                .chain(tau_points),
        );

        // debug
        // assert_eq!(check3, rho[2]);

        if check3 != rho[2] {
            return Err(ProofError::VerificationError);
        }

        Ok(())
    }
}

/// Matrix multiplication
/// This assumes a is column-major and b is row-major, as used in first reduction step.
/// a should have n rows and b should have k columns
pub fn tp_mat_mult(a: &[Scalar], b: &[Scalar], n: usize, k: usize) -> Vec<Scalar> {
    let mut c = Vec::with_capacity(n * k);

    for i in 0..n {
        for j in 0..k {
            let witness_a_rightow = a.iter().skip(i).step_by(n);
            let b_col = b.iter().skip(j).step_by(k);
            let mut val = Scalar::zero();
            for (a_val, b_val) in witness_a_rightow.zip(b_col) {
                val += a_val * b_val;
            }
            c.push(val);
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

//TODO: CURRENT
pub fn reduction_lambda_1(
    public: (
        &mut [RistrettoPoint],
        &mut [RistrettoPoint],
        &mut [RistrettoPoint],
        RistrettoPoint,
    ),
    witness: (&mut [Scalar], &mut [Scalar], &mut [Scalar], Scalar),
) -> (CompressedRistretto, CompressedRistretto, Scalar, Scalar) {
    let public_G = public.0;
    let public_H = public.1;
    let public_U = public.2;
    let g_0 = public.3;
    let witness_a = witness.0;
    let witness_b = witness.1;
    let c = witness.2;
    let blinding_r = witness.3;

    let mut rng = rand::thread_rng();

    let t = Scalar::random(&mut rng);
    let q = blinding_r - t;
    let blinding_r = t;

    let alpha = RistrettoPoint::vartime_multiscalar_mul(
        witness_a.iter().chain(c.iter()).chain(iter::once(&q)),
        public_G
            .iter()
            .chain(public_U.iter())
            .chain(iter::once(&g_0)),
    )
    .compress();

    let beta = RistrettoPoint::vartime_multiscalar_mul(
        witness_b.iter().chain(iter::once(&blinding_r)),
        public_H.iter().chain(iter::once(&g_0)),
    )
    .compress();

    (alpha, beta, blinding_r, q)
}

pub fn reduction_lambda_2(
    public: (&mut [RistrettoPoint], &mut [RistrettoPoint], RistrettoPoint),
    witness: (&mut [Scalar], &mut [Scalar], Scalar),
) -> (CompressedRistretto, CompressedRistretto, Scalar, Scalar) {
    let public_G = public.0;
    let public_U = public.1;
    let g_0 = public.2;
    let witness_a = witness.0;
    let c = witness.1;
    let q = witness.2;

    let mut rng = rand::thread_rng();
    let s = Scalar::random(&mut rng);
    let t = q - s; //TODO:  TEMP

    let sigma = RistrettoPoint::vartime_multiscalar_mul(
        witness_a.iter().chain(iter::once(&t)),
        public_G.iter().chain(iter::once(&g_0)),
    )
    .compress();

    let tau = RistrettoPoint::vartime_multiscalar_mul(
        c.iter().chain(iter::once(&s)),
        public_U.iter().chain(iter::once(&g_0)),
    )
    .compress();

    (sigma, tau, q, s)
}

/// Get generators: for use in benchmarks and other cases where external code
/// must access generators
pub fn get_gens(
    n: usize,
    m: usize,
    k: usize,
) -> (
    Vec<RistrettoPoint>,
    Vec<RistrettoPoint>,
    Vec<RistrettoPoint>,
    RistrettoPoint,
) {
    use crate::generators::MatrixFoldingGens;
    let mf_gens = MatrixFoldingGens::new(n, m, k);
    let G: Vec<RistrettoPoint> = mf_gens.G();
    let H: Vec<RistrettoPoint> = mf_gens.H();
    let U: Vec<RistrettoPoint> = mf_gens.U();
    let g_0 = mf_gens.g_0().unwrap();
    (G, H, U, g_0)
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let g_0 = mf_gens.g_0().unwrap();

        // a and b are the matrices for which we want to prove c=ab
        // just generate random matrices every time
        let a: Vec<_> = (0..(n * m)).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..(m * k)).map(|_| Scalar::random(&mut rng)).collect();
        let c = tp_mat_mult(&a, &b, n, k);
        let r = Scalar::random(&mut rng);

        // Compute commitment P
        let P = RistrettoPoint::vartime_multiscalar_mul(
            a.iter()
                .chain(b.iter())
                .chain(c.iter())
                .chain(iter::once(&r)),
            G.iter()
                .chain(H.iter())
                .chain(U.iter())
                .chain(iter::once(&g_0)),
        );

        // generate proof
        let mut prover = Transcript::new(b"matrixfoldingtest");
        let proof = ZKMatrixFoldingProof::create(
            &mut prover,
            (G.clone(), H.clone(), U.clone(), g_0.clone()),
            (a.clone(), b.clone(), r.clone()),
            (n, m, k),
        );

        // verify proof
        let mut verifier = Transcript::new(b"matrixfoldingtest");
        assert!(proof
            .verify(&mut verifier, &P, &G[..], &H[..], &U[..], &g_0, n, m, k)
            .is_ok());
    }

    #[test]
    fn make_mfp_1() {
        mfp_test_helper_create(1, 1, 1);
    }

    #[test]
    fn make_mfp_2() {
        mfp_test_helper_create(16, 1, 1);
    }

    #[test]
    fn make_mfp_3() {
        mfp_test_helper_create(1, 1, 16);
    }

    #[test]
    fn make_mfp_4() {
        mfp_test_helper_create(16, 1, 16);
    }

    #[test]
    fn make_mfp_5() {
        mfp_test_helper_create(16, 1, 32);
    }

    #[test]
    fn make_mfp_6() {
        mfp_test_helper_create(1, 16, 1);
    }

    #[test]
    fn make_mfp_7() {
        mfp_test_helper_create(8, 16, 1);
    }

    #[test]
    fn make_mfp_8() {
        mfp_test_helper_create(1, 16, 8);
    }

    #[test]
    fn make_mfp_9() {
        mfp_test_helper_create(32, 4, 8);
    }

    #[test]
    fn make_mfp_10() {
        mfp_test_helper_create(64, 64, 64);
    }

    // for testing multiplication
    fn col_to_row(a: &Vec<Scalar>, n: usize, m: usize) -> Vec<Scalar> {
        let mut aT = vec![Scalar::zero(); n * m];
        for row in 0..n {
            for col in 0..m {
                aT[m * row + col] = a[n * col + row];
            }
        }
        aT
    }

    fn row_to_col(b: &Vec<Scalar>, m: usize, k: usize) -> Vec<Scalar> {
        let mut bT = vec![Scalar::zero(); m * k];
        for row in 0..m {
            for col in 0..k {
                bT[m * col + row] = b[k * row + col];
            }
        }
        bT
    }

    fn tp_mat_mult_test_helper(n: usize, m: usize, k: usize) {
        let mut rng = rand::thread_rng();
        let a: Vec<_> = (0..(n * m)).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..(m * k)).map(|_| Scalar::random(&mut rng)).collect();
        let c = tp_mat_mult(&a, &b, n, k);

        let aT = col_to_row(&a, n, m);
        let bT = row_to_col(&b, m, k);
        for x in 0..n {
            for y in 0..k {
                assert_eq!(
                    inner_product(&aT[x * m..(x + 1) * m], &bT[y * m..(y + 1) * m]),
                    c[k * x + y]
                );
            }
        }
    }

    #[test]
    fn tp_mm_test_1() {
        tp_mat_mult_test_helper(1, 1, 1);
    }

    #[test]
    fn tp_mm_test_2() {
        tp_mat_mult_test_helper(16, 1, 1);
    }

    #[test]
    fn tp_mm_test_3() {
        tp_mat_mult_test_helper(1, 1, 16);
    }

    #[test]
    fn tp_mm_test_4() {
        tp_mat_mult_test_helper(16, 1, 16);
    }

    #[test]
    fn tp_mm_test_5() {
        tp_mat_mult_test_helper(1, 16, 1);
    }

    #[test]
    fn tp_mm_test_6() {
        tp_mat_mult_test_helper(16, 32, 1);
    }

    #[test]
    fn tp_mm_test_7() {
        tp_mat_mult_test_helper(1, 32, 16);
    }

    #[test]
    fn tp_mm_test_8() {
        tp_mat_mult_test_helper(64, 32, 16);
    }

    #[test]
    fn tp_mm_test_9() {
        tp_mat_mult_test_helper(2, 2, 2);
    }
}
