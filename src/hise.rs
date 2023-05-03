use bls12_381::{pairing, G1Projective, G2Projective, Scalar, Gt};
use pairing::group::{Curve, GroupEncoding};
use ff::*;
use rand::{thread_rng};
use std::{ops::{Add, Mul, Neg}};

use crate::polynomial::*;
use crate::utils;

type HiseWitnessCommitment = (G2Projective, G2Projective);

pub struct HiseNizkProofParams {
    pub g: G2Projective,
    pub h: G2Projective,
}

impl <'a> HiseNizkProofParams {
    pub fn new() -> HiseNizkProofParams {
        let mut rng = thread_rng();

        let g = G2Projective::generator();
        
        loop {
            let r = Scalar::random(&mut rng);
            //avoid degenerate points
            if r == Scalar::from(0 as u64) {
                continue;
            }
            let h = g.mul(&r);
            return HiseNizkProofParams { g, h };
        }
    }
}

pub struct HiseEncNizkProof {
    pub ut1: G2Projective,
    pub ut2: G2Projective,
    pub αz1: Scalar,
    pub αz2: Scalar,
}

pub struct HiseDecNizkProof {
    pub ut1: G2Projective,
    pub ut2: G2Projective,
    pub αz1: Scalar,
    pub αz2: Scalar,
}

pub struct HiseEncNizkStatement {
    pub g: G2Projective,
    pub h: G2Projective,
    pub h_of_x_eps: G2Projective, //H(x_eps)
    pub h_of_x_eps_pow_a: G2Projective, //H(x_eps)^a 
    pub com: G2Projective, //ped com g^a. h^b
}

pub struct HiseDecNizkStatement {
    pub g: G2Projective,
    pub h: G2Projective,
    pub h_of_x_eps: G2Projective, //H(x_eps)
    pub h_of_x_eps_pow_a: G2Projective, //H(x_eps)^a 
    pub com: G2Projective, //ped com g^a. h^b
}

pub struct HiseNizkWitness {
    pub α1: Scalar,
    pub α2: Scalar,
    pub β1: Scalar,
    pub β2: Scalar,
}

impl <'a> HiseEncNizkProof {

    fn random_oracle(
        ut1: &G2Projective, 
        ut2: &G2Projective
    ) -> Scalar {
        let mut bytes = vec![];
    
        bytes.extend_from_slice(&ut1.to_bytes().as_ref());
        bytes.extend_from_slice(&ut2.to_bytes().as_ref());
    
        utils::hash_to_scalar(&bytes)
    }

    // exists α1, α2 s.t. \phi(α1,α2) = true
    // \phi(x1, x2) := { com = g^{α1}.h^{α2} ∧ prfEval = H(x)^{α1} }
    pub fn prove(
        witness: &HiseNizkWitness,
        stmt: &HiseEncNizkStatement
    ) -> HiseEncNizkProof {
        let mut rng = thread_rng();
        let αt1 = Scalar::random(&mut rng);
        let αt2 = Scalar::random(&mut rng);

        let ut1 = stmt.h_of_x_eps.mul(αt1);
        let ut2 = stmt.g.mul(αt1).add(stmt.h.mul(αt2));

        //TODO: this needs more inputs
        let c = HiseEncNizkProof::random_oracle(&ut1, &ut2);

        let αz1 = αt1 + c * witness.α1;
        let αz2 = αt2 + c * witness.α2;

        HiseEncNizkProof { ut1, ut2, αz1, αz2 }
    }

    pub fn verify(
        stmt: &HiseEncNizkStatement,
        proof: &HiseEncNizkProof,
    ) -> bool {
        let c = HiseEncNizkProof::random_oracle(&proof.ut1, &proof.ut2);
        
        let lhs1 = stmt.h_of_x_eps.mul(&proof.αz1);
        let rhs1 = proof.ut1.add(stmt.h_of_x_eps_pow_a.mul(&c));

        let lhs2 = stmt.g.mul(&proof.αz1).add(stmt.h.mul(&proof.αz2));
        let rhs2 = proof.ut2.add(stmt.com.mul(&c));

        return lhs1 == rhs1 && lhs2 == rhs2;
    }
}

/* 
impl <'a> AtseDecNizkProof {

    fn random_oracle(
        ut1: &Gt, 
        ut2: &Gt
    ) -> Scalar {
        let mut bytes = vec![];
    
        bytes.extend_from_slice(&ut1.to_compressed().as_ref());
        bytes.extend_from_slice(&ut2.to_compressed().as_ref());
    
        utils::hash_to_scalar(&bytes)
    }

    // exists α1, α2 s.t. \phi(α1,α2) = true
    // \phi(x1, x2) := { com = g^{α1}.h^{α2} ∧ prfEval = H(x)^{α1} }
    pub fn prove(
        witness: &AtseNizkWitness,
        stmt: &AtseDecNizkStatement
    ) -> AtseDecNizkProof {
        let mut rng = thread_rng();
        let αt1 = Scalar::random(&mut rng);
        let αt2 = Scalar::random(&mut rng);

        let ut1 = stmt.e_base.mul(αt1);
        let ut2 = stmt.egg.mul(αt1).add(stmt.egh.mul(αt2));

        //TODO: this needs more inputs
        let c = AtseDecNizkProof::random_oracle(&ut1, &ut2);

        let αz1 = αt1 + c * witness.α1;
        let αz2 = αt2 + c * witness.α2;

        AtseDecNizkProof { ut1, ut2, αz1, αz2 }
    }

    pub fn verify(
        stmt: &AtseDecNizkStatement,
        proof: &AtseDecNizkProof,
    ) -> bool {
        let c = AtseDecNizkProof::random_oracle(&proof.ut1, &proof.ut2);
        
        let lhs1 = stmt.e_base.mul(&proof.αz1);
        let rhs1 = proof.ut1.add(stmt.e_base_pow_a.mul(&c));

        let lhs2 = stmt.egg.mul(&proof.αz1).add(stmt.egh.mul(&proof.αz2));
        let rhs2 = proof.ut2.add(stmt.com.mul(&c));

        return lhs1 == rhs1 && lhs2 == rhs2;
    }
}
*/

pub struct Hise { }

impl Hise {
    pub fn setup(n: usize, t: usize) -> 
    (HiseNizkProofParams, Vec<HiseNizkWitness>, Vec<HiseWitnessCommitment>) {
        let mut rng = rand::thread_rng();

        let pp = HiseNizkProofParams::new();

        let p1 = utils::sample_random_poly(&mut rng, t - 1);
        let p2 = utils::sample_random_poly(&mut rng, t - 1);
        let p3 = utils::sample_random_poly(&mut rng, t - 1);
        let p4 = utils::sample_random_poly(&mut rng, t - 1);

        let mut private_keys = vec![];
        let mut commitments = vec![];

        for i in 1..=n {
            let x = Scalar::from(i as u64);
            let α1_i = p1.eval(&x);
            let α2_i = p2.eval(&x);
            let β1_i = p3.eval(&x);
            let β2_i = p4.eval(&x);

            let witness = HiseNizkWitness { 
                α1: α1_i,
                α2: α2_i,
                β1: β1_i,
                β2: β2_i,
            };
            private_keys.push(witness);

            let com_α = utils::pedersen_commit_in_g2(
                &pp.g, &pp.h, &α1_i, &α2_i);
            let com_β = utils::pedersen_commit_in_g2(
                &pp.g, &pp.h, &β1_i, &β2_i);
            commitments.push((com_α, com_β));
        }
        (pp, private_keys, commitments)
    }

    fn get_random_data_commitment() -> [u8; 32] {
        use rand::prelude::*;
        let mut rng = rand::thread_rng();
        let mut array = [0u8; 32];
        rng.fill(&mut array);
        array
    }

    pub fn encrypt_server(
        pp: &HiseNizkProofParams, 
        key: &HiseNizkWitness,
        com: &HiseWitnessCommitment
    ) -> (HiseEncNizkStatement, HiseEncNizkProof) {
        // γ should come from the client, 
        // but it doesnt matter for perf testing 
        let γ = Hise::get_random_data_commitment();
        let h_of_γ = utils::hash_to_g2(&γ);
        let h_of_γ_pow_α1 = h_of_γ.mul(key.α1);
        let stmt = HiseEncNizkStatement {
            g: pp.g.clone(),
            h: pp.h.clone(),
            h_of_x_eps: h_of_γ,
            h_of_x_eps_pow_a: h_of_γ_pow_α1,
            com: com.0.clone()
        };

        let proof = HiseEncNizkProof::prove(&key, &stmt);
        return (stmt, proof);
    }

    /* 
    pub fn decrypt_server(
        pp: &AtseNizkProofParams, 
        key: &AtseNizkWitness,
        com: &AtseWitnessCommitment
    ) -> (AtseDecNizkStatement, AtseDecNizkProof) {
        // γ and q should come from the client, 
        // but it doesnt matter for perf testing 
        let γ = Atse::get_random_data_commitment();
        let q = Atse::get_random_data_commitment();

        let h_of_γ = utils::hash_to_g1(&γ);
        let h_of_q = utils::hash_to_g2(&q);

        let e_base = pairing(
            &h_of_γ.to_affine(), 
            &h_of_q.to_affine()
        );

        let stmt = AtseDecNizkStatement {
            egg: pp.egg.clone(),
            egh: pp.egh.clone(),
            e_base: e_base,
            e_base_pow_a: e_base.mul(&key.α1),
            com: com.1.clone()
        };

        let proof = AtseDecNizkProof::prove(key, &stmt);
        return (stmt, proof);
    }
    */

    pub fn encrypt_client(
        m: usize, //number of messages
        server_responses: &Vec<(HiseEncNizkStatement, HiseEncNizkProof)>) {
        //first verify all the proofs
        for (stmt, proof) in server_responses {
            assert!(HiseEncNizkProof::verify(stmt, proof));
        }

        //now compute the lagrange coefficients
        let n = server_responses.len();
        let all_xs: Vec<Scalar> = (1..=n)
            .into_iter()
            .map(|x| Scalar::from(x as u64))
            .collect();
        let coeffs: Vec<Scalar> = Polynomial::lagrange_coefficients(all_xs.as_slice());

        //compute the interpolated DPRF evaluation
        let solo_evals: Vec<G2Projective> = server_responses.
            iter().
            map(|(s,p)| s.h_of_x_eps_pow_a.clone()).
            collect();

        //this is called z in the paper
        let gk = utils::multi_exp_g2(solo_evals.as_slice(), &coeffs.as_slice()[0..n]);
        // credit chatgpt: This function takes a floating-point number x as input and 
        // returns the logarithm base 2 of x, rounded up to the nearest integer. 
        let log_m = (m as f64).log2().ceil() as u64;

        //for each of the m ciphertexts, we need to do log m work
        let mut rng = thread_rng();
        let g1 = G1Projective::generator();
        for i in 0..m {
            let r_j = Scalar::random(&mut rng);
            let g1_pow_r_j = g1.mul(&r_j);
            
            for j in 0..log_m {
                let x_w_j = Hise::get_random_data_commitment();
                let h_of_x_w_j = utils::hash_to_g2(x_w_j.as_slice());
                let h_of_x_w_j_pow_r_j = h_of_x_w_j.mul(&r_j);
                let mk_j = pairing(&g1_pow_r_j.to_affine(), &gk.to_affine());
            }
        }
    }

    /*
    pub fn decrypt_client(
        server_responses: &Vec<(AtseDecNizkStatement, AtseDecNizkProof)>) {
        //first verify all the proofs
        for (stmt, proof) in server_responses {
            assert!(AtseDecNizkProof::verify(stmt, proof));
        }

        //now compute the lagrange coefficients
        let n = server_responses.len();
        let all_xs: Vec<Scalar> = (1..=n)
            .into_iter()
            .map(|x| Scalar::from(x as u64))
            .collect();
        let coeffs: Vec<Scalar> = Polynomial::lagrange_coefficients(all_xs.as_slice());

        //compute the interpolated DPRF evaluation
        let solo_evals: Vec<Gt> = server_responses.
            iter().
            map(|(s,p)| s.e_base_pow_a.clone()).
            collect();

        let _ = utils::multi_exp_gt(solo_evals.as_slice(), &coeffs.as_slice()[0..n]);
    }
    */

}

#[cfg(test)]
pub mod tests {
    use super::*;
    use rand::{thread_rng};
    use std::time::{Instant};

    #[test]
    fn test_enc_performance() {
        let t = 5; let n = 5; //number of nodes
        let m = 100; // number of messages

        let (pp, keys, coms) = Hise::setup(n, t);

        let mut server_responses = vec![];
        for i in 0..n {
            let (stmt, proof) = Hise::encrypt_server(&pp, &keys[i], &coms[i]);
            server_responses.push((stmt, proof));
        }

        let now = Instant::now();
        let _ = Hise::encrypt_server(&pp, &keys[0], &coms[0]);
        Hise::encrypt_client(m, &server_responses);
        let duration = now.elapsed();
        println!("DiSE encrypt for {} nodes and {} messages: {} s {} ms",
                t, m, duration.as_secs(), duration.as_millis());
    }

    /*
    #[test]
    fn test_dec_performance() {
        let t = 5; let n = 5; //number of nodes
        let m = 100; // number of messages

        let (pp, keys, coms) = Atse::setup(n, t);

        let mut server_responses = vec![];
        for i in 0..n {
            let (stmt, proof) = Atse::decrypt_server(&pp, &keys[i], &coms[i]);
            server_responses.push((stmt, proof));
        }

        let now = Instant::now();
        for i in 0..m {
            let _ = Atse::decrypt_server(&pp, &keys[0], &coms[0]);
            Atse::decrypt_client(&server_responses);
        }
        let duration = now.elapsed();
        println!("DiSE decrypt for {} nodes and {} messages: {} s {} ms",
                t, m, duration.as_secs(), duration.as_millis());
    }
    */

    #[test]
    fn test_correctness_enc_nizk() {
        let mut rng = thread_rng();

        let α1 = Scalar::random(&mut rng);
        let α2 = Scalar::random(&mut rng);
        let β1 = Scalar::random(&mut rng);
        let β2 = Scalar::random(&mut rng);
        let witness = HiseNizkWitness { α1, α2, β1, β2 };

        let pp = HiseNizkProofParams::new();
        let h_of_x_eps = utils::hash_to_g2(&[0; 32]);
        let stmt = HiseEncNizkStatement {
            g: pp.g.clone(),
            h: pp.h.clone(),
            h_of_x_eps: h_of_x_eps,
            h_of_x_eps_pow_a: h_of_x_eps.mul(&α1),
            com: utils::pedersen_commit_in_g2(&pp.g, &pp.h, &α1, &α2)
        };
        let proof = HiseEncNizkProof::prove(&witness, &stmt);
        let check = HiseEncNizkProof::verify(&stmt, &proof);
        assert!(check);
    }

    /* 
    #[test]
    fn test_correctness_dec_nizk() {
        let mut rng = thread_rng();

        let α1 = Scalar::random(&mut rng);
        let α2 = Scalar::random(&mut rng);
        let witness = AtseNizkWitness { α1, α2 };

        let h_of_x = utils::hash_to_g1(Atse::get_random_data_commitment().as_slice());
        let h_of_q = utils::hash_to_g2(Atse::get_random_data_commitment().as_slice());
        let e_base = pairing(&h_of_x.to_affine(), &h_of_q.to_affine());

        let pp = AtseNizkProofParams::new();
        let stmt = AtseDecNizkStatement {
            egg: pp.egg.clone(),
            egh: pp.egh.clone(),
            e_base: e_base,
            e_base_pow_a: e_base.mul(&α1),
            com: utils::pedersen_commit_in_gt(&pp.egg, &pp.egh, &α1, &α2)
        };
        let proof = AtseDecNizkProof::prove(&witness, &stmt);
        let check = AtseDecNizkProof::verify(&stmt, &proof);
        assert!(check);
    }
    */
}
