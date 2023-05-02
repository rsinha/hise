use bls12_381::{pairing, G1Projective, G2Projective, Scalar};
use pairing::group::{
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding, UncompressedEncoding,
};
use ff::*;
use rand::{thread_rng};
use std::collections::{BTreeMap};
use std::ops::{Add, Mul, Neg};

use crate::polynomial::*;
use crate::utils;
use crate::universe::*;
use crate::common::sig_utils;
use crate::{XCoord, UniverseId, PartyId, Weight, PartyPublicKey, AddressBook};

type DiseWitnessCommitment = G1Projective;

pub struct DiseNizkProof {
    pub ut1: G1Projective,
    pub ut2: G1Projective,
    pub αz1: Scalar,
    pub αz2: Scalar,
}

pub struct DiseNizkProofParams {
    pub g: G1Projective,
    pub h: G1Projective
}

pub struct DiseNizkStatement {
    pub g: G1Projective,
    pub h: G1Projective,
    pub h_of_x: G1Projective, //H(x)
    pub h_of_x_pow_a: G1Projective, //H(x)^s 
    pub com: G1Projective, //ped com g^a. h^b
}

pub struct DiseNizkWitness {
    pub α1: Scalar,
    pub α2: Scalar,
}

impl <'a> DiseNizkProofParams {
    pub fn new() -> DiseNizkProofParams {
        let mut rng = thread_rng();
        let g = G1Projective::generator();
        loop {
            let r = Scalar::random(&mut rng);
            //avoid degenerate points
            if r == Scalar::from(0 as u64) {
                continue;
            }
            let h = g.mul(&r);
            return DiseNizkProofParams { g, h };
        }
    }
}


impl <'a> DiseNizkProof {

    fn random_oracle(
        ut1: &G1Projective, 
        ut2: &G1Projective
    ) -> Scalar {
        let mut bytes = vec![];
    
        bytes.extend_from_slice(&ut1.to_bytes().as_ref());
        bytes.extend_from_slice(&ut2.to_bytes().as_ref());
    
        utils::hash_to_scalar(&bytes)
    }

    // exists α1, α2 s.t. \phi(α1,α2) = true
    // \phi(x1, x2) := { com = g^{α1}.h^{α2} ∧ prfEval = H(x)^{α1} }
    pub fn prove(
        witness: &DiseNizkWitness,
        stmt: &DiseNizkStatement
    ) -> DiseNizkProof {
        let mut rng = thread_rng();
        let αt1 = Scalar::random(&mut rng);
        let αt2 = Scalar::random(&mut rng);

        let ut1 = stmt.h_of_x.mul(αt1);
        let ut2 = stmt.g.mul(αt1).add(stmt.h.mul(αt2));

        //TODO: this needs more inputs
        let c = DiseNizkProof::random_oracle(
            &ut1, &ut2);

        let αz1 = αt1 + c * witness.α1;
        let αz2 = αt2 + c * witness.α2;

        DiseNizkProof { ut1, ut2, αz1, αz2 }
    }

    pub fn verify(
        stmt: &DiseNizkStatement,
        proof: &DiseNizkProof,
    ) -> bool {
        let c = DiseNizkProof::random_oracle(
            &proof.ut1, &proof.ut2);
        
        let lhs1 = stmt.h_of_x.mul(&proof.αz1);
        let rhs1 = proof.ut1.add(stmt.h_of_x_pow_a.mul(&c));

        let lhs2 = stmt.g.mul(&proof.αz1).add(stmt.h.mul(&proof.αz2));
        let rhs2 = proof.ut2.add(stmt.com.mul(&c));

        return lhs1 == rhs1 && lhs2 == rhs2;
    }
}

pub struct Dise { }

impl Dise {
    pub fn setup(n: usize, t: usize) -> 
    (DiseNizkProofParams, Vec<DiseNizkWitness>, Vec<DiseWitnessCommitment>) {
        let mut rng = rand::thread_rng();

        let pp = DiseNizkProofParams::new();

        let p1 = sig_utils::sample_random_poly(&mut rng, t - 1);
        let p2 = sig_utils::sample_random_poly(&mut rng, t - 1);

        let mut private_keys = vec![];
        let mut commitments = vec![];

        for i in 1..=n {
            let x = Scalar::from(i as u64);
            let α1_i = p1.eval(&x);
            let α2_i = p2.eval(&x);

            let witness = DiseNizkWitness { 
                α1: p1.eval(&x),
                α2: p2.eval(&x)
            };
            private_keys.push(witness);

            let com = utils::pedersen_commit_in_g1(
                &pp.g, &pp.h, &α1_i, &α2_i);
            commitments.push(com);
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
        pp: &DiseNizkProofParams, 
        key: &DiseNizkWitness,
        com: &DiseWitnessCommitment,
    ) -> (DiseNizkStatement, DiseNizkProof) {

        let γ = Dise::get_random_data_commitment();
        let h_of_γ = utils::hash_to_g1(&γ);
        let h_of_γ_pow_α1 = h_of_γ.mul(key.α1);
        let stmt = DiseNizkStatement {
            g: pp.g.clone(),
            h: pp.h.clone(),
            h_of_x: h_of_γ,
            h_of_x_pow_a: h_of_γ_pow_α1,
            com: com.clone()
        };

        let proof = DiseNizkProof::prove(&key, &stmt);
        return (stmt, proof);
    }

    pub fn encrypt_client(server_responses: &Vec<(DiseNizkStatement, DiseNizkProof)>) {
        //first verify all the proofs
        for (stmt, proof) in server_responses {
            assert!(DiseNizkProof::verify(stmt, proof));
        }

        //now compute the lagrange coefficients
        let n = server_responses.len();
        let all_xs: Vec<Scalar> = (1..=n)
            .into_iter()
            .map(|x| Scalar::from(x as u64))
            .collect();
        let coeffs: Vec<Scalar> = Polynomial::lagrange_coefficients(all_xs.as_slice());

        //compute the interpolated DPRF evaluation
        let solo_evals: Vec<G1Projective> = server_responses.
            iter().
            map(|(s,p)| s.h_of_x_pow_a.clone()).
            collect();

        let _ = utils::multi_exp_g1(solo_evals.as_slice(), &coeffs.as_slice()[0..n]);
    }

}

#[cfg(test)]
pub mod tests {
    use super::*;
    use rand::{thread_rng};
    use std::time::{Instant};

    #[test]
    fn test_performance() {
        let t = 5; let n = 5; //number of nodes
        let m = 100; // number of messages

        let (pp, keys, coms) = Dise::setup(n, t);

        let mut server_responses = vec![];
        for i in 0..n {
            let (stmt, proof) = Dise::encrypt_server(&pp, &keys[i], &coms[i]);
            server_responses.push((stmt, proof));
        }

        let now = Instant::now();

        for i in 0..m {
            //since servers operate in parallel, we include the time to execute 1 server
            let _ = Dise::encrypt_server(&pp, &keys[0], &coms[0]);
            //client must process all servers responses
            Dise::encrypt_client(&server_responses);
        }

        let duration = now.elapsed();
        println!("DiSE encrypt for {} nodes and {} messages: {} s {} ms",
                t, m, duration.as_secs(), duration.as_millis());
    }

    #[test]
    fn test_correctness_enc_dec() {
        let t = 50; let n = 50;
        let (pp, keys, coms) = Dise::setup(n, t);
        let mut server_responses = vec![];
        for i in 0..n {
            let (stmt, proof) = Dise::encrypt_server(&pp, &keys[i], &coms[i]);
            server_responses.push((stmt, proof));
        }
        Dise::encrypt_client(&server_responses);
    }

    #[test]
    fn test_correctness_nizk() {
        let mut rng = thread_rng();

        let α1 = Scalar::random(&mut rng);
        let α2 = Scalar::random(&mut rng);
        let witness = DiseNizkWitness { α1, α2 };

        let pp = DiseNizkProofParams::new();
        let h_of_x = utils::hash_to_g1(&[0; 32]);
        let h_of_x_pow_α1 = h_of_x.mul(&α1);
        let com = utils::pedersen_commit_in_g1(&pp.g, &pp.h, &α1, &α2);
        let stmt = DiseNizkStatement {
            g: pp.g.clone(),
            h: pp.h.clone(),
            h_of_x: h_of_x,
            h_of_x_pow_a: h_of_x_pow_α1,
            com: com
        };
        let proof = DiseNizkProof::prove(&witness, &stmt);
        let check = DiseNizkProof::verify(&stmt, &proof);
        assert!(check);
    }
}
