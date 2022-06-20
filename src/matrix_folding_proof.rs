#![allow(non_snake_case)]
#![allow(dead_code)]
#![cfg_attr(feature = "docs", doc(include = "../docs/inner-product-protocol.md"))]
extern crate alloc;

use alloc::borrow::Borrow;
use alloc::vec::Vec;

use core::iter;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::transcript::TranscriptProtocol;

#[derive(Clone, Debug)]
pub struct MatrixFoldingProof {
    pub(crate) L_vec1: Vec<CompressedRistretto>,
    pub(crate) R_vec1: Vec<CompressedRistretto>,
    pub(crate) L_vec3: Vec<CompressedRistretto>,
    pub(crate) R_vec3: Vec<CompressedRistretto>,
    pub(crate) L_vec2: Vec<CompressedRistretto>,
    pub(crate) R_vec2: Vec<CompressedRistretto>,
    pub(crate) a: Scalar,
    pub(crate) b: Scalar,
}

impl MatrixFoldingProof {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut Transcript,
        mut G_vec: Vec<RistrettoPoint>, // say these are stored in row-major
        mut H_vec: Vec<RistrettoPoint>,
        mut U_vec: Vec<RistrettoPoint>, // this used to be Q and was not a vector nor mutable
        mut a_vec: Vec<Scalar>,
        mut b_vec: Vec<Scalar>, // I WILL ASSUME b CONTAINS THE TRANSPOSE OF THE MATRIX B!!!!
        mut n: usize, //not sure if these need to be mutable but I'm assuming yes
        mut m: usize,
        mut k: usize
    ) -> MatrixFoldingProof {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut U = &mut U_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let one = Scalar::one();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n*m);
        assert_eq!(H.len(), m*k);
        assert_eq!(U.len(), n*k);
        assert_eq!(a.len(), n*m);
        assert_eq!(b.len(), m*k);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());
        assert!(m.is_power_of_two());
        assert!(k.is_power_of_two());

        transcript.matrixfolding_domain_sep(n as u64, m as u64, k as u64); 

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let lg_m = m.next_power_of_two().trailing_zeros() as usize; 
        let lg_k = k.next_power_of_two().trailing_zeros() as usize;
        
        let mut L_vec1 = Vec::with_capacity(lg_n);
        let mut R_vec1 = Vec::with_capacity(lg_n);
        let mut L_vec3 = Vec::with_capacity(lg_k);
        let mut R_vec3 = Vec::with_capacity(lg_k);
        let mut L_vec2 = Vec::with_capacity(lg_m);
        let mut R_vec2 = Vec::with_capacity(lg_m);


        // compute C (or else we'd need to have it passed in as argument)
        let mut c_vec = mat_mult(a, b, n, k);
        let mut c = &mut c_vec[..];

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

            // compute a', G'
            for i in 1..(n*m) {
                a_t[i] = x * a_t[i] + a_b[i];
                G_t[i] = RistrettoPoint::vartime_multiscalar_mul(&[x_inv, one], &[G_t[i], G_b[i]]);
            }

            // compute c', U'
            for i in 1..(n*k) {
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

            for i in 1..(m*k) {
                b_l[i] = x * b_l[i] + b_r[i];
                H_l[i] = RistrettoPoint::vartime_multiscalar_mul(&[x_inv, one], &[H_l[i], H_r[i]]);
            }

            for i in 1..k {
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

        while m != 1 {
            m = m/2;
            let (a_l, a_r) = a.split_at_mut(m);
            let (b_t, b_b) = b.split_at_mut(m);
            let (G_l, G_r) = G.split_at_mut(m);
            let (H_t, H_b) = H.split_at_mut(m);

            let c_l = inner_product(a_l, b_b);
            let c_r = inner_product(a_r, b_t);

            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_l.iter().chain(b_t.iter().chain(iter::once(&c_l))), 
                G_r.iter().chain(H_b.iter().chain(U.iter()))
            ).compress(); // at this point U should have length 1

            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_r.iter().chain(b_b.iter().chain(iter::once(&c_r))), 
                G_l.iter().chain(H_t.iter().chain(U.iter()))
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

            for i in 1..m {
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
        MatrixFoldingProof {
            L_vec1: L_vec1,
            R_vec1: R_vec1,
            L_vec3: L_vec3,
            R_vec3: R_vec3,
            L_vec2: L_vec2,
            R_vec2: R_vec2,
            a: a[0],
            b: b[0],
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

        // 1. Recompute x_k,...,x_1 based on the proof transcript

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
        /* 
        let mut challengesG = challenges1.clone();
        challengesG.extend(&challenges2);
        let mut challengesH = challenges3.clone();
        challengesH.extend(&challenges2);
        let mut challengesU = challenges1.clone();
        challengesU.extend(&challenges3);

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1
        
        let mut challengesG_inv = challengesG.clone();
        let allinvG = Scalar::batch_invert(&mut challengesG_inv);
        let mut challengesH_inv = challengesH.clone();
        let allinvH = Scalar::batch_invert(&mut challengesH_inv);
        let mut challengesU_inv = challengesU.clone();
        let allinvU = Scalar::batch_invert(&mut challengesU_inv);

        let mut challenges_inv = challenges1.clone();
        challenges_inv.extend(&challenges3);
        challenges_inv.extend(&challenges2);
        let allinv = Scalar::batch_invert(&mut challenges_inv);
        */
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

        // 3. Compute u_i^2 and (1/u_i)^2

        /* WE DON'T NEED SQUARES because we made better choices
        for i in 0..lg_n {
            // XXX missing square fn upstream
            challenges[i] = challenges[i] * challenges[i];
            challenges_inv[i] = challenges_inv[i] * challenges_inv[i];
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;
        */
        // 4. Compute s values inductively.

        let mut s_G = Vec::with_capacity(n*m);
        let mut s_H = Vec::with_capacity(m*k);
        let mut s_U = Vec::with_capacity(n*k);

        // compute G scalars (I think this code works fine just ripped straight from original)
        s_G.push(s_G0);
        for i in 1..(n*m) {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i; 
            let x_lg_i = challengesG[(lg_n + lg_m - 1) - lg_i];
            s_G.push(s_G[i - k] * x_lg_i);
        }

        s_H.push(s_H0);
        for i in 1..(m*k) {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i; 
            let x_lg_i = challengesH[(lg_m + lg_k - 1) - lg_i];
            s_H.push(s_H[i - k] * x_lg_i);
        }

        s_U.push(s_U0); 
        for i in 1..(m*n) {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            let x_lg_i = challengesU[(lg_n + lg_m - 1) - lg_i];
            s_U.push(s_U[i - k] * x_lg_i);
        }
        // TODO still have to figure out exactly what must be returned...
        Ok((challenges1, challenges3, challenges2, challenges1_inv, challenges3_inv, challenges2_inv, s_G, s_H, s_U))
    }

    /// This method is for testing that proof generation works,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify<IG, IH>(
        &self,
        transcript: &mut Transcript,
        P: &RistrettoPoint,
        G: &[RistrettoPoint],
        H: &[RistrettoPoint],
        U: &[RistrettoPoint],
        n: usize,
        m: usize,
        k: usize
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<Scalar>,
        IH: IntoIterator,
        IH::Item: Borrow<Scalar>,
    {
        let (x1, x3, x2, x1_inv, x3_inv, x2_inv, s_G, s_H, s_U) = self.verification_scalars(n, m, k, transcript)?;

        let g_exp = s_G.iter().map(|s_i| self.a * s_i);
        let h_exp = s_H.iter().map(|s_i| self.b * s_i);
        let c = self.a * self.b;
        let u_exp = s_U.iter().map(|s_i| c * s_i);

        let neg_x = x1.iter()
            .chain(x3.iter())
            .chain(x2.iter())
            .map(|xi| -xi);
        let neg_x_inv = x1_inv.iter()
            .chain(x3_inv.iter())
            .chain(x2_inv.iter())
            .map(|xi| -xi);

        let Ls = self
            .L_vec1
            .iter()
            .chain(self.L_vec3
            .iter())
            .chain(self.L_vec2
            .iter())
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = self
            .R_vec1
            .iter()
            .chain(self.R_vec3
            .iter())
            .chain(self.R_vec2
            .iter())
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

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

        if expect_P == *P {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }
    // pretty sure everything after here is not needed for testing
/*
    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    ///
    /// For vectors of length `n` the proof size is
    /// \\(32 \cdot (2\lg n+2)\\) bytes.
    pub fn serialized_size(&self) -> usize {
        (self.L_vec.len() * 2 + 2) * 32
    }

    /// Serializes the proof into a byte array of \\(2n+2\\) 32-byte elements.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            buf.extend_from_slice(l.as_bytes());
            buf.extend_from_slice(r.as_bytes());
        }
        buf.extend_from_slice(self.a.as_bytes());
        buf.extend_from_slice(self.b.as_bytes());
        buf
    }

    /// Converts the proof into a byte iterator over serialized view of the proof.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    #[inline]
    pub(crate) fn to_bytes_iter(&self) -> impl Iterator<Item = u8> + '_ {
        self.L_vec
            .iter()
            .zip(self.R_vec.iter())
            .flat_map(|(l, r)| l.as_bytes().iter().chain(r.as_bytes()))
            .chain(self.a.as_bytes())
            .chain(self.b.as_bytes())
            .copied()
    }

    /// Deserializes the proof from a byte slice.
    /// Returns an error in the following cases:
    /// * the slice does not have \\(2n+2\\) 32-byte elements,
    /// * \\(n\\) is larger or equal to 32 (proof is too big),
    /// * any of \\(2n\\) points are not valid compressed Ristretto points,
    /// * any of 2 scalars are not canonical scalars modulo Ristretto group order.
     pub fn from_bytes(slice: &[u8]) -> Result<MatrixFoldingProof, ProofError> {
        let b = slice.len();
        if b % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        let num_elements = b / 32;
        if num_elements < 2 {
            return Err(ProofError::FormatError);
        }
        if (num_elements - 2) % 2 != 0 {
            return Err(ProofError::FormatError);
        }
        let lg_n = (num_elements - 2) / 2;
        if lg_n >= 32 {
            return Err(ProofError::FormatError);
        }

        use crate::util::read32;

        let mut L_vec: Vec<CompressedRistretto> = Vec::with_capacity(lg_n);
        let mut R_vec: Vec<CompressedRistretto> = Vec::with_capacity(lg_n);
        for i in 0..lg_n {
            let pos = 2 * i * 32;
            L_vec.push(CompressedRistretto(read32(&slice[pos..])));
            R_vec.push(CompressedRistretto(read32(&slice[pos + 32..])));
        }

        let pos = 2 * lg_n * 32;
        let a =
            Scalar::from_canonical_bytes(read32(&slice[pos..])).ok_or(ProofError::FormatError)?;
        let b = Scalar::from_canonical_bytes(read32(&slice[pos + 32..]))
            .ok_or(ProofError::FormatError)?;

        Ok(MatrixFoldingProof { L_vec, R_vec, a, b })
    }
*/
}

// I will assume the matrices are Vec<Scalar>s, rather than [Sacalar]s.
// Also: I assume a is row-major, b is a row-major representation of b TRANSPOSE
// so we want to calculate a*b, but we are given the transpose of b as input
// result will be stored in c, which should come in EMPTY
// a should have n rows and b should have k columns (so b transpose should have k rows)
fn mat_mult(a: &[Scalar], b: &[Scalar], n: usize, k: usize) -> Vec<Scalar> {
    let mut c = Vec::with_capacity(n*k);
    let m = a.len()/n;
    assert_eq!(m, b.len()/k);
    for a_row in a.chunks(m) {
        for b_col in b.chunks(m) {
            let mut val = Scalar::zero();
            for i in 0..m {
                val += a_row[i] * b_col[i];
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

#[cfg(test)]
mod tests {
    use super::*;

    use crate::util;
    use sha3::Sha3_512;

    fn test_helper_create(n: usize, m: usize, k: usize) {
        let mut rng = rand::thread_rng();

        use crate::generators::MatrixFoldingGens;
        let mf_gens = MatrixFoldingGens::new(n, m, k);
        let G: Vec<RistrettoPoint> = mf_gens.G().clone();
        let H: Vec<RistrettoPoint> = mf_gens.H().clone();
        let U: Vec<RistrettoPoint> = mf_gens.U().clone();

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..(n*m)).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..(m*k)).map(|_| Scalar::random(&mut rng)).collect();
        let c = mat_mult(&a, &b, n, k);

        // P would be determined upstream, but we need a correct P to check the proof.
        //
        // To generate P = <a,G> + <b,H'> + <a,b> Q, compute
        //             P = <a,G> + <b',H> + <a,b> Q,
        // where b' = b \circ y^(-n)
        let b_prime = b.iter().zip(util::exp_iter(y_inv)).map(|(bi, yi)| bi * yi);
        // a.iter() has Item=&Scalar, need Item=Scalar to chain with b_prime
        let a_prime = a.iter().cloned();

        let P = RistrettoPoint::vartime_multiscalar_mul(
            a_prime.chain(b_prime).chain(iter::once(c)),
            G.iter().chain(H.iter()).chain(iter::once(&Q)),
        );

        let mut verifier = Transcript::new(b"innerproducttest");
        let proof = MatrixFoldingProof::create(
            &mut verifier,
            &Q,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        );

        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                n,
                &mut verifier,
                iter::repeat(Scalar::one()).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &Q,
                &G,
                &H
            )
            .is_ok());

        let proof = MatrixFoldingProof::from_bytes(proof.to_bytes().as_slice()).unwrap();
        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                n,
                &mut verifier,
                iter::repeat(Scalar::one()).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &Q,
                &G,
                &H
            )
            .is_ok());
    }

    #[test]
    fn make_ipp_1() {
        test_helper_create(1);
    }

    #[test]
    fn make_ipp_2() {
        test_helper_create(2);
    }

    #[test]
    fn make_ipp_4() {
        test_helper_create(4);
    }

    #[test]
    fn make_ipp_32() {
        test_helper_create(32);
    }

    #[test]
    fn make_ipp_64() {
        test_helper_create(64);
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product(&a, &b));
    }
}

