#![allow(non_snake_case)]
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
    pub(crate) L_vec: Vec<CompressedRistretto>,
    pub(crate) R_vec: Vec<CompressedRistretto>,
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

        transcript.innerproduct_domain_sep(n as u64); // TODO this is not going to work, idk how to use transcripts though :(

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let lg_m = m.next_power_of_two().trailing_zeros() as usize; 
        let lg_k = k.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n + lg_m + lg_k); // theoretically number of iterations is sum of logs of dimensions?
        let mut R_vec = Vec::with_capacity(lg_n + lg_m + lg_k);
        
        // compute C (or else we'd need to have it passed in as argument)
        let mut c_vec = Vec::with_capacity(n*k);
        mat_mult(a, b, &mut c_vec, n, k);
        let mut c = &mut c_vec[..];

        // all subsequent iterations besides first happen here (first happens above) 
        // (unless first is n=1, in which case both above and below blocks skipped)
        // start by doing all the protocol 1 folds we can before moving on
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
            L_vec.push(L);
            R_vec.push(R);

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


        // now fold B
        // Technically we need to find transpose of C, but since A is now row vector, C is a row vector, so we can just
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
            L_vec.push(L);
            R_vec.push(R);

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
        

        // return value
        // note proof keeps its own record of L and R terms from each iteration, separate from transcript
        MatrixFoldingProof {
            L_vec: L_vec,
            R_vec: R_vec,
            a: a[0],
            b: b[0],
        }
    }

    /// splitting methods
    fn split_vertically(a: &mut [Scalar], m: usize) -> (&'_ mut [Scalar], &'_ mut [Scalar]) {
        // this one should be easier...
        a.split_at_mut(m/2)
        // lol
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
        transcript: &mut Transcript,
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), ProofError> {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript
        // idk it looks like their notation is inconsistent, here they talk about x but I think they mean what they're calling u... 
        // maybe got confused with the paper's notation ??

        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges.push(transcript.challenge_scalar(b"u"));
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1

        let mut challenges_inv = challenges.clone();
        let allinv = Scalar::batch_invert(&mut challenges_inv);

        // 3. Compute u_i^2 and (1/u_i)^2

        for i in 0..lg_n {
            // XXX missing square fn upstream
            challenges[i] = challenges[i] * challenges[i];
            challenges_inv[i] = challenges_inv[i] * challenges_inv[i];
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;

        // 4. Compute s values inductively.

        let mut s = Vec::with_capacity(n);
        s.push(allinv);
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i; // bitwise shift for exp
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            s.push(s[i - k] * u_lg_i_sq);
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

    /// This method is for testing that proof generation work,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify<IG, IH>(
        &self,
        n: usize,
        transcript: &mut Transcript,
        G_factors: IG,
        H_factors: IH,
        P: &RistrettoPoint,
        Q: &RistrettoPoint,
        G: &[RistrettoPoint],
        H: &[RistrettoPoint],
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<Scalar>,
        IH: IntoIterator,
        IH::Item: Borrow<Scalar>,
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| (self.a * s_i) * g_i.borrow())
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| (self.b * s_i_inv) * h_i.borrow());

        let neg_u_sq = u_sq.iter().map(|ui| -ui);
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| -ui);

        let Ls = self
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = self
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let expect_P = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(self.a * self.b)
                .chain(g_times_a_times_s)
                .chain(h_times_b_div_s)
                .chain(neg_u_sq)
                .chain(neg_u_inv_sq),
            iter::once(Q)
                .chain(G.iter())
                .chain(H.iter())
                .chain(Ls.iter())
                .chain(Rs.iter()),
        );

        if expect_P == *P {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

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
    pub fn from_bytes(slice: &[u8]) -> Result<InnerProductProof, ProofError> {
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

        Ok(InnerProductProof { L_vec, R_vec, a, b })
    }
}

// I will assume the matrices are Vec<Scalar>s, rather than [Sacalar]s.
// Also: I assume a is row-major, b is a row-major representation of b TRANSPOSE
// so we want to calculate a*b, but we are given the transpose of b as input
// result will be stored in c, which should come in EMPTY
// a should have n rows and b should have k columns (so b transpose should have k rows)
fn mat_mult(a: &[Scalar], b: &[Scalar], c: &mut Vec<Scalar>, n: usize, k: usize) {
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

    fn test_helper_create(n: usize) {
        let mut rng = rand::thread_rng();

        use crate::generators::BulletproofGens;
        let bp_gens = BulletproofGens::new(n, 1);
        let G: Vec<RistrettoPoint> = bp_gens.share(0).G(n).cloned().collect();
        let H: Vec<RistrettoPoint> = bp_gens.share(0).H(n).cloned().collect();

        // Q would be determined upstream in the protocol, so we pick a random one.
        let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let c = inner_product(&a, &b);

        let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(n).collect();

        // y_inv is (the inverse of) a random challenge
        let y_inv = Scalar::random(&mut rng);
        let H_factors: Vec<Scalar> = util::exp_iter(y_inv).take(n).collect();

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
        let proof = InnerProductProof::create(
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

        let proof = InnerProductProof::from_bytes(proof.to_bytes().as_slice()).unwrap();
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
