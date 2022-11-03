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
    //TODO temp
    // pub(crate) alpha: CompressedRistretto,
    // pub(crate) beta: CompressedRistretto,
    // pub(crate) sigma: CompressedRistretto,
    // pub(crate) tau: CompressedRistretto,
    // pub(crate) rho_vec: Vec<CompressedRistretto>,
    // pub(crate) z_vec: Vec<Scalar>, // These are for debugging purposes only, will be removed lated
}

#[derive(Debug, Clone)]
pub struct PublicParameters {
    dim_n: usize,
    dim_m: usize,
    dim_k: usize,
    vec_g: Vec<RistrettoPoint>,
    vec_h: Vec<RistrettoPoint>,
    vec_u: Vec<RistrettoPoint>,
    g_0: RistrettoPoint,
}

pub struct SecretInputs {
    vec_a: Vec<Scalar>,
    vec_b: Vec<Scalar>,
    r: Scalar,
}

impl ZKMatrixFoldingProof {
    /// Create a matrix folding proof.
    ///
    /// The Verifier is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The dimnsions of the matrices must all be powers of 2
    pub fn create(
        transcript: &mut Transcript,
        public_parameters: &mut PublicParameters,
        secret_inputs: &mut SecretInputs,
    ) -> ZKMatrixFoldingProof {
        // Create slices G, H, a, b backed by their respective
        // vectors. This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        //TODO: I don't like this
        let mut G = &mut public_parameters.vec_g[..];
        let mut H = &mut public_parameters.vec_h[..];
        let mut U = &mut public_parameters.vec_u[..];
        let mut a = &mut secret_inputs.vec_a[..];
        let mut b = &mut secret_inputs.vec_b[..];

        let one = Scalar::one();

        // for generating random blinding factors
        let mut rng = rand::thread_rng();

        // All of the input vectors must have the correct length
        assert_eq!(G.len(), public_parameters.dim_n * public_parameters.dim_m);
        assert_eq!(H.len(), public_parameters.dim_m * public_parameters.dim_k);
        assert_eq!(U.len(), public_parameters.dim_n * public_parameters.dim_k);
        assert_eq!(a.len(), public_parameters.dim_n * public_parameters.dim_m);
        assert_eq!(b.len(), public_parameters.dim_m * public_parameters.dim_k);

        // All of the dimensions of matrices must be a power of two.
        assert!(public_parameters.dim_n.is_power_of_two());
        assert!(public_parameters.dim_m.is_power_of_two());
        assert!(public_parameters.dim_k.is_power_of_two());

        transcript.matrixfolding_domain_sep(
            public_parameters.dim_n as u64,
            public_parameters.dim_m as u64,
            public_parameters.dim_k as u64,
        );

        //TODO: Why this?
        let lg_n = public_parameters.dim_n.next_power_of_two().trailing_zeros() as usize;
        let lg_m = public_parameters.dim_m.next_power_of_two().trailing_zeros() as usize;
        let lg_k = public_parameters.dim_k.next_power_of_two().trailing_zeros() as usize;

        // create vectors for L and R values TODO: effective?
        let mut L_vec1 = Vec::with_capacity(lg_m);
        let mut R_vec1 = Vec::with_capacity(lg_m);
        let mut L_vec2 = Vec::with_capacity(lg_n);
        let mut R_vec2 = Vec::with_capacity(lg_n);
        let mut L_vec3_beta = Vec::with_capacity(lg_k);
        let mut R_vec3_beta = Vec::with_capacity(lg_k);
        let mut L_vec3_tau = Vec::with_capacity(lg_k);
        let mut R_vec3_tau = Vec::with_capacity(lg_k);

        // first fold A and B with inner product approach
        // This requires that A is column-major so that the split is done correct.
        while public_parameters.dim_m != 1 {
            red_phi1(
                &mut transcript,
                &mut public_parameters,
                &mut secret_inputs,
                &mut L_vec1,
                &mut R_vec1,
            );
        }

        //TODO: why set r = t?
        // now for "mini-reduction" 1, to transform the commitments
        let t = Scalar::random(&mut rng);
        let mut q = secret_inputs.r - t;
        secret_inputs.r = t;

        let mut c = &mut tp_mat_mult(a, b, public_parameters.dim_n, public_parameters.dim_k)[..];

        /*
        let alpha = RistrettoPoint::vartime_multiscalar_mul(
            a.iter().chain(c.iter()).chain(iter::once(&q)),
            G.iter().chain(U.iter()).chain(iter::once(&g_0)),
        )
        .compress();

        let beta = RistrettoPoint::vartime_multiscalar_mul(
            b.iter().chain(iter::once(&r)),
            H.iter().chain(iter::once(&g_0)),
        )
        .compress();

        transcript.append_point(b"a", &alpha);
        transcript.append_point(b"b", &beta);
        */

        // Now, fold n (A)
        // A now holds a col vector, so can fold vertically easily

        while public_parameters.dim_n != 1 {
            red_phi2(
                &mut transcript,
                &mut public_parameters,
                &mut secret_inputs,
                &mut L_vec2,
                &mut R_vec2,
            );
        }

        // mini-reduction 2: transform commitments again
        let t = Scalar::random(&mut rng);
        q = q - t;
        let mut s = t;

        let sigma = RistrettoPoint::vartime_multiscalar_mul(
            a.iter().chain(iter::once(&q)),
            G.iter().chain(iter::once(&public_parameters.g_0)),
        )
        .compress();

        let tau = RistrettoPoint::vartime_multiscalar_mul(
            c.iter().chain(iter::once(&s)),
            U.iter().chain(iter::once(&public_parameters.g_0)),
        )
        .compress();

        transcript.append_point(b"s", &sigma);
        transcript.append_point(b"t", &tau);

        // now fold k/B
        /*
                while k != 1 {
                    k = k / 2;
                    let (b_l, b_r) = b.split_at_mut(k);
                    let (c_l, c_r) = c.split_at_mut(k); // n == 1 by the time we get here
                    let (H_l, H_r) = H.split_at_mut(k);
                    let (U_l, U_r) = U.split_at_mut(k);

                    // blinding
                    let r_l = Scalar::random(&mut rng);
                    let r_r = Scalar::random(&mut rng);
                    let s_l = Scalar::random(&mut rng);
                    let s_r = Scalar::random(&mut rng);

                    // commitments: note we have 4 here, since we need 2 for beta and 2 for tau
                    let L_beta = RistrettoPoint::vartime_multiscalar_mul(
                        b_l.iter().chain(iter::once(&r_l)),
                        H_r.iter().chain(iter::once(&g_0)),
                    )
                    .compress();

                    let R_beta = RistrettoPoint::vartime_multiscalar_mul(
                        b_r.iter().chain(iter::once(&r_r)),
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
                    for i in 0..k {
                        b_l[i] = z * b_l[i] + b_r[i];
                        H_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[z_inv, one], &[H_l[i], H_r[i]]);
                    }

                    // compute new c, U
                    for i in 0..k {
                        // n == 1
                        c_l[i] = z * c_l[i] + c_r[i];
                        U_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[z_inv, one], &[U_l[i], U_r[i]]);
                    }
                    // compute + update blindings
                    r = (z * r_l) + r + (z_inv * r_r);
                    s = (z * s_l) + s + (z_inv * s_r);

                    // update values
                    b = b_l;
                    c = c_l;
                    H = H_l;
                    U = U_l;
                }
        */
        // final ZK scalar mult step

        /*
        // compute blinding factors and commitments
        let t: Vec<_> = (0..5).map(|_| Scalar::random(&mut rng)).collect();
        let rho_0 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&t[0]).chain(iter::once(&t[1])),
            G.iter().chain(iter::once(&g_0)),
        )
        .compress();
        let rho_1 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&t[2]).chain(iter::once(&t[3])),
            H.iter().chain(iter::once(&g_0)),
        )
        .compress();
        let rho_2 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&(t[0] * t[2])).chain(iter::once(&t[4])),
            U.iter().chain(iter::once(&g_0)),
        )
        .compress();
        let rho_3 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&(t[0] * b[0] + t[2] * a[0])),
            U.iter(),
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
        let z_0 = t[0] + (a[0] * x);
        let z_1 = t[1] + (q * x);
        let z_2 = t[2] + (b[0] * x);
        let z_3 = t[3] + (r * x);
        let z_4 = t[4] + (s * x * x);

        let z_vec = vec![z_0, z_1, z_2, z_3, z_4];
        */
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
            //alpha,
            //beta,
            //sigma,
            //tau,
            //rho_vec,
            //z_vec, // fields below will be removed, for debugging only
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
        let lg_m = self.L_vec1.len();
        let lg_n = self.L_vec2.len();
        let lg_k = self.L_vec3_beta.len();

        if lg_n >= 32 || lg_m >= 32 || lg_k >= 32 {
            // prevent overflow in bitshifts later on
            return Err(ProofError::VerificationError);
        }
        if (lg_n != 0 && n != (1 << lg_n))
            || (lg_m != 0 && m != (1 << lg_m))
            || (lg_k != 0 && k != (1 << lg_k))
        {
            // not powers of 2
            return Err(ProofError::VerificationError);
        }
        if self.L_vec3_tau.len() != lg_k
            || self.R_vec3_beta.len() != lg_k
            || self.R_vec3_tau.len() != lg_k
        {
            // malformed vectors
            return Err(ProofError::VerificationError);
        }

        //debug
        // println!("Verification_scalars passed first checks");

        transcript.matrixfolding_domain_sep(n as u64, m as u64, k as u64);

        // 1. Recompute challenges based on the proof transcript
        // add everything to transcript and get challenges, just like the Prover does

        let mut challenges1 = Vec::with_capacity(lg_m);
        let mut challenges2 = Vec::with_capacity(lg_n);
        let mut challenges3 = Vec::with_capacity(lg_k);

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
            transcript.validate_and_append_point(b"bL", &L_beta)?;
            transcript.validate_and_append_point(b"bR", &R_beta)?;
            transcript.validate_and_append_point(b"tL", &L_tau)?;
            transcript.validate_and_append_point(b"tR", &R_tau)?;
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
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << lg_i;
            let x_lg_i = challengesG[(lg_n + lg_m - 1) - lg_i];
            s_G.push(s_G[i - b] * x_lg_i);
        }

        s_H.push(s_H0);
        for i in 1..(m * k) {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << lg_i;
            let x_lg_i = challengesH[(lg_m + lg_k - 1) - lg_i];
            s_H.push(s_H[i - b] * x_lg_i);
        }

        s_U.push(s_U0);
        for i in 1..(n * k) {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let b = 1 << lg_i;
            let x_lg_i = challengesU[(lg_n + lg_k - 1) - lg_i];
            s_U.push(s_U[i - b] * x_lg_i);
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

        //let one = Scalar::one();
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
            x1.iter()
                .chain(x1_inv.iter())
                .chain(iter::once(&Scalar::one())),
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
        let alpha_Ls = self
            .L_vec2
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let alpha_Rs = self
            .R_vec2
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let alpha_final = RistrettoPoint::vartime_multiscalar_mul(
            x2.iter()
                .chain(x2_inv.iter())
                .chain(iter::once(&Scalar::one())),
            alpha_Ls
                .iter()
                .chain(alpha_Rs.iter())
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
        let beta_Ls = self
            .L_vec3_beta
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let beta_Rs = self
            .R_vec3_beta
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        let beta_points = beta_Ls
            .iter()
            .chain(beta_Rs.iter())
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
            .chain(iter::once(&Scalar::one()))
            .map(|x| x * neg_zk_mult_chall);

        let tau_exp = x3
            .iter()
            .chain(x3_inv.iter())
            .chain(iter::once(&Scalar::one()))
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
            G.iter()
                .chain(iter::once(&public_parameters.g_0))
                .chain(iter::once(&sigma)),
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

pub fn red_phi1(
    transcript: &mut Transcript,
    public_parameters: &mut PublicParameters,
    secret_inputs: &mut SecretInputs,
    L_vec1: &mut Vec<CompressedRistretto>,
    R_vec1: &mut Vec<CompressedRistretto>,
) {
    let mut rng = rand::thread_rng();

    public_parameters.dim_m /= 2;
    let (a_l, a_r) =
        secret_inputs.vec_a[..].split_at_mut(public_parameters.dim_m * public_parameters.dim_n);
    let (b_t, b_b) =
        secret_inputs.vec_b[..].split_at_mut(public_parameters.dim_m * public_parameters.dim_k);
    let (G_l, G_r) =
        public_parameters.vec_g[..].split_at_mut(public_parameters.dim_m * public_parameters.dim_n);
    let (H_t, H_b) =
        public_parameters.vec_h[..].split_at_mut(public_parameters.dim_m * public_parameters.dim_k);

    // get cross terms for L and R
    // these are matrix multiplications :(
    let c_l = tp_mat_mult(a_l, b_b, public_parameters.dim_n, public_parameters.dim_k);
    let c_r = tp_mat_mult(a_r, b_t, public_parameters.dim_n, public_parameters.dim_k);

    // gemerate blinding factors for L and R
    let r_l = Scalar::random(&mut rng);
    let r_r = Scalar::random(&mut rng);

    // compute L and R
    let L = RistrettoPoint::vartime_multiscalar_mul(
        a_l.iter()
            .chain(b_b.iter())
            .chain(c_l.iter())
            .chain(iter::once(&r_l)),
        G_r.iter()
            .chain(H_t.iter())
            .chain(public_parameters.vec_u.iter())
            .chain(iter::once(&public_parameters.g_0)),
    )
    .compress();

    let R = RistrettoPoint::vartime_multiscalar_mul(
        a_r.iter()
            .chain(b_t.iter())
            .chain(c_r.iter())
            .chain(iter::once(&r_r)),
        G_l.iter()
            .chain(H_b.iter())
            .chain(public_parameters.vec_u.iter())
            .chain(iter::once(&public_parameters.g_0)),
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

    // update witnesses and public parameters for recursion
    for i in 0..(public_parameters.dim_n * public_parameters.dim_m) {
        a_l[i] = x * a_l[i] + a_r[i];
        G_l[i] =
            RistrettoPoint::vartime_multiscalar_mul(&[x_inv, Scalar::one()], &[G_l[i], G_r[i]]);
    }

    for i in 0..(public_parameters.dim_m * public_parameters.dim_k) {
        b_t[i] = x_inv * b_t[i] + b_b[i];
        H_t[i] = RistrettoPoint::vartime_multiscalar_mul(&[x, Scalar::one()], &[H_t[i], H_b[i]]);
    }

    secret_inputs.r += (x * r_l) + (x_inv * r_r);
    //TODO: bah
    secret_inputs.vec_a = a_l;
    secret_inputs.vec_b = b_t;
    public_parameters.vec_g = G_l;
    public_parameters.vec_h = H_t;
}

pub fn red_phi2(
    transcript: &mut Transcript,
    public_parameters: &mut PublicParameters,
    secret_inputs: &mut SecretInputs,
    L_vec2: &mut Vec<CompressedRistretto>,
    R_vec2: &mut Vec<CompressedRistretto>,
) {
    let mut rng = rand::thread_rng();

    public_parameters.dim_n /= 2;
    let (a_t, a_b) = secret_inputs.vec_a[..].split_at_mut(public_parameters.dim_n);
    //TODO fix
    let (c_t, c_b) = c[..].split_at_mut(public_parameters.dim_n * public_parameters.dim_k);
    let (G_t, G_b) = public_parameters.vec_g[..].split_at_mut(public_parameters.dim_n);
    let (U_t, U_b) =
        public_parameters.vec_u[..].split_at_mut(public_parameters.dim_n * public_parameters.dim_k);

    // gemerate blinding factors for L and R
    let q_l = Scalar::random(&mut rng);
    let q_r = Scalar::random(&mut rng);

    // compute L and R
    let L = RistrettoPoint::vartime_multiscalar_mul(
        a_t.iter().chain(c_t.iter()).chain(iter::once(&q_l)),
        G_b.iter()
            .chain(U_b.iter())
            .chain(iter::once(&public_parameters.g_0)),
    )
    .compress();

    let R = RistrettoPoint::vartime_multiscalar_mul(
        a_b.iter().chain(c_b.iter()).chain(iter::once(&q_r)),
        G_t.iter()
            .chain(U_t.iter())
            .chain(iter::once(&public_parameters.g_0)),
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
    for i in 0..public_parameters.dim_n {
        a_t[i] = y * a_t[i] + a_b[i];
        G_t[i] =
            RistrettoPoint::vartime_multiscalar_mul(&[y_inv, Scalar::one()], &[G_t[i], G_b[i]]);
    }

    // compute new c, U
    for i in 0..(public_parameters.dim_n * public_parameters.dim_k) {
        c_t[i] = y * c_t[i] + c_b[i];
        U_t[i] =
            RistrettoPoint::vartime_multiscalar_mul(&[y_inv, Scalar::one()], &[U_t[i], U_b[i]]);
    }

    // compute and update q
    q += (y * q_l) + (y_inv * q_r);

    // update a, c, G, U
    secret_inputs.vec_a = a_t;
    c = c_t;
    public_parameters.vec_g = G_t;
    public_parameters.vec_u = U_t;
}

/// Matrix multiplication
/// This assumes a is column-major and b is row-major, as used in first reduction step.
/// a should have n rows and b should have k columns
pub fn tp_mat_mult(a: &[Scalar], b: &[Scalar], n: usize, k: usize) -> Vec<Scalar> {
    let mut c = Vec::with_capacity(n * k);

    for i in 0..n {
        for j in 0..k {
            let a_row = a.iter().skip(i).step_by(n);
            let b_col = b.iter().skip(j).step_by(k);
            let mut val = Scalar::zero();
            for (a_val, b_val) in a_row.zip(b_col) {
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
            G.clone(),
            H.clone(),
            U.clone(),
            g_0.clone(),
            a.clone(),
            b.clone(),
            r.clone(),
            n,
            m,
            k,
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
