use bls12_381::{pairing, G1Projective, G2Projective, Scalar, Gt};
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

type AtseWitnessCommitment = (G1Projective, Gt);

pub struct AtseNizkProofParams {
    pub g: G1Projective,
    pub h: G1Projective,
    pub egg: Gt,
    pub egh: Gt
}

impl <'a> AtseNizkProofParams {
    pub fn new() -> AtseNizkProofParams {
        let mut rng = thread_rng();

        let g = G1Projective::generator();
        let egg = Gt::generator();
        
        loop {
            let r = Scalar::random(&mut rng);
            //avoid degenerate points
            if r == Scalar::from(0 as u64) {
                continue;
            }

            let h = g.mul(&r);
            let egh = egg.mul(&r);

            return AtseNizkProofParams { g, h, egg, egh };
        }
    }
}


pub struct AtseEncNizkProof {
    pub ut1: G1Projective,
    pub ut2: G1Projective,
    pub αz1: Scalar,
    pub αz2: Scalar,
}

pub struct AtseDecNizkProof {
    pub ut1: Gt,
    pub ut2: Gt,
    pub αz1: Scalar,
    pub αz2: Scalar,
}

pub struct AtseEncNizkStatement {
    pub g: G1Projective,
    pub h: G1Projective,
    pub h_of_x: G1Projective, //H(x)
    pub h_of_x_pow_a: G1Projective, //H(x)^s 
    pub com: G1Projective, //ped com g^a. h^b
}

pub struct AtseDecNizkStatement {
    pub egg: Gt,
    pub egh: Gt,
    pub e_base: Gt, //e(H(gamma), H(q))
    pub e_base_pow_a: Gt, //e(H(gamma), H(q))^s 
    pub com: Gt, //ped com egg^a. egh^b
}

pub struct AtseNizkWitness {
    pub α1: Scalar,
    pub α2: Scalar,
}

impl <'a> AtseEncNizkProof {

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
        witness: &AtseNizkWitness,
        stmt: &AtseEncNizkStatement
    ) -> AtseEncNizkProof {
        let mut rng = thread_rng();
        let αt1 = Scalar::random(&mut rng);
        let αt2 = Scalar::random(&mut rng);

        let ut1 = stmt.h_of_x.mul(αt1);
        let ut2 = stmt.g.mul(αt1).add(stmt.h.mul(αt2));

        //TODO: this needs more inputs
        let c = AtseEncNizkProof::random_oracle(
            &ut1, &ut2);

        let αz1 = αt1 + c * witness.α1;
        let αz2 = αt2 + c * witness.α2;

        AtseEncNizkProof { ut1, ut2, αz1, αz2 }
    }

    pub fn verify(
        stmt: &AtseEncNizkStatement,
        proof: &AtseEncNizkProof,
    ) -> bool {
        let c = AtseEncNizkProof::random_oracle(
            &proof.ut1, &proof.ut2);
        
        let lhs1 = stmt.h_of_x.mul(&proof.αz1);
        let rhs1 = proof.ut1.add(stmt.h_of_x_pow_a.mul(&c));

        let lhs2 = stmt.g.mul(&proof.αz1).add(stmt.h.mul(&proof.αz2));
        let rhs2 = proof.ut2.add(stmt.com.mul(&c));

        return lhs1 == rhs1 && lhs2 == rhs2;
    }
}

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


pub struct Atse { }

impl Atse {
    pub fn setup(n: usize, t: usize) -> 
    (AtseNizkProofParams, Vec<AtseNizkWitness>, Vec<AtseWitnessCommitment>) {
        let mut rng = rand::thread_rng();

        let pp = AtseNizkProofParams::new();

        let p1 = utils::sample_random_poly(&mut rng, t - 1);
        let p2 = utils::sample_random_poly(&mut rng, t - 1);

        let mut private_keys = vec![];
        let mut commitments = vec![];

        for i in 1..=n {
            let x = Scalar::from(i as u64);
            let α1_i = p1.eval(&x);
            let α2_i = p2.eval(&x);

            let witness = AtseNizkWitness { 
                α1: p1.eval(&x),
                α2: p2.eval(&x)
            };
            private_keys.push(witness);

            let com_g1 = utils::pedersen_commit_in_g1(
                &pp.g, &pp.h, &α1_i, &α2_i);
            let com_gt = utils::pedersen_commit_in_gt(
                &pp.egg, &pp.egh, &α1_i, &α2_i);
            commitments.push((com_g1, com_gt));
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
        pp: &AtseNizkProofParams, 
        key: &AtseNizkWitness,
        com: &AtseWitnessCommitment
    ) -> (AtseEncNizkStatement, AtseEncNizkProof) {
        // γ should come from the client, 
        // but it doesnt matter for perf testing 
        let γ = Atse::get_random_data_commitment();
        let h_of_γ = utils::hash_to_g1(&γ);
        let h_of_γ_pow_α1 = h_of_γ.mul(key.α1);
        let stmt = AtseEncNizkStatement {
            g: pp.g.clone(),
            h: pp.h.clone(),
            h_of_x: h_of_γ,
            h_of_x_pow_a: h_of_γ_pow_α1,
            com: com.0.clone()
        };

        let proof = AtseEncNizkProof::prove(&key, &stmt);
        return (stmt, proof);
    }

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

    pub fn encrypt_client(
        m: usize, //number of messages
        server_responses: &Vec<(AtseEncNizkStatement, AtseEncNizkProof)>) {
        //first verify all the proofs
        for (stmt, proof) in server_responses {
            assert!(AtseEncNizkProof::verify(stmt, proof));
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

        let gk = utils::multi_exp_g1(solo_evals.as_slice(), &coeffs.as_slice()[0..n]);

        for i in 0..m {
            let q_i = Atse::get_random_data_commitment();
            let h_of_q_i = utils::hash_to_g2(q_i.as_slice());

            let mk_i = pairing(&gk.to_affine(), &h_of_q_i.to_affine());
        }
    }

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

}

#[cfg(test)]
pub mod tests {
    use super::*;
    use rand::{thread_rng};
    use std::time::{Instant};

    #[test]
    fn test_enc_latency() {
        // n = 6,12,18.24
        let rows = [[2,4,6,8], [3,6,9,12], [4,8,12,16]];
        for row in rows.iter() {
            for t in row.iter() {
                let t = *t as usize; let n = t;

                let mut measurements = vec![];
                for m in [1, 100, 10000].iter() {
                    let m = *m as usize;

                    let (pp, keys, coms) = Atse::setup(n, t);

                    let mut server_responses = vec![];
                    for i in 0..n {
                        let (stmt, proof) = Atse::encrypt_server(&pp, &keys[i], &coms[i]);
                        server_responses.push((stmt, proof));
                    }
            
                    let now = Instant::now();
                    let _ = Atse::encrypt_server(&pp, &keys[0], &coms[0]);
                    Atse::encrypt_client(m, &server_responses);
                    let duration = now.elapsed();
                    println!("ATSE encrypt for {} nodes and {} messages: {} seconds",
                            t, m, duration.as_secs_f32());
                            measurements.push(duration.as_secs_f32());
                }
                print!("t = {}: ", t);
                for latency in measurements.iter() {
                    print!("{:.3} & ", latency);
                }
                print!("\n");
            }
        }
    }

    #[test]
    fn test_dec_latency() {
        // n = 6,12,18.24
        let rows = [[2,4,6,8], [3,6,9,12], [4,8,12,16]];
        for row in rows.iter() {
            for t in row.iter() {
                let t = *t as usize; let n = t;

                let mut measurements = vec![];
                for m in [1, 100].iter() {
                    let m = *m as usize;

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
                    println!("ATSE decrypt for {} nodes and {} messages: {} seconds",
                            t, m, duration.as_secs_f32());
                            measurements.push(duration.as_secs_f32());
                }
                print!("t = {}: ", t);
                for latency in measurements.iter() {
                    print!("{:.5} & ", latency);
                }
                print!("\n");
            }
        }
    }

    #[test]
    fn test_dec_throughput() {
        let num_cpu = 16;
        let rows = [[2,2,6,8], [3,6,9,12], [4,8,12,16]];
        for row in rows.iter() {
            for t in row.iter() {
                let t = *t as usize; let n = t;

                let mut measurements = vec![];
                for m in [1, 1, 10000].iter() {
                    let m = *m as usize;

                    let (pp, keys, coms) = Atse::setup(n, t);

                    let mut server_responses = vec![];
                    for i in 0..n {
                        let (stmt, proof) = Atse::decrypt_server(&pp, &keys[i], &coms[i]);
                        server_responses.push((stmt, proof));
                    }
            
                    let now = Instant::now();
                    for i in 0..m {
                        Atse::decrypt_client(&server_responses);
                    }
                    let duration = now.elapsed().as_secs_f32();
                    let throughput = (num_cpu as f32) * ((m as f32) / duration);
                    println!("ATSE throughput for {} nodes and {} messages: {} seconds; {} enc/sec",
                            t, m, duration, throughput);
                    measurements.push(throughput);
                }
                print!("t = {}: ", t);
                for throughput in measurements.iter() {
                    print!("{:.3} & ", throughput);
                }
                print!("\n");
            }
        }
    }


    #[test]
    fn test_enc_throughput() {
        let num_cpu = 16;
        let rows = [[2,4,6,8], [3,6,9,12], [4,8,12,16]];
        for row in rows.iter() {
            for t in row.iter() {
                let t = *t as usize; let n = t;

                let mut measurements = vec![];
                for m in [1, 100, 10000].iter() {
                    let m = *m as usize;

                    let (pp, keys, coms) = Atse::setup(n, t);

                    let mut server_responses = vec![];
                    for i in 0..n {
                        let (stmt, proof) = Atse::encrypt_server(&pp, &keys[i], &coms[i]);
                        server_responses.push((stmt, proof));
                    }
            
                    let now = Instant::now();
                    Atse::encrypt_client(m, &server_responses);
                    let duration = now.elapsed().as_secs_f32();
                    let throughput = (num_cpu as f32) * ((m as f32) / duration);
                    println!("ATSE throughput for {} nodes and {} messages: {} seconds; {} enc/sec",
                            t, m, duration, throughput);
                    measurements.push(throughput);
                }
                print!("t = {}: ", t);
                for throughput in measurements.iter() {
                    print!("{:.3} & ", throughput);
                }
                print!("\n");
            }
        }
    }

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

    #[test]
    fn test_correctness_enc_dec() {
        let t = 50; let n = 50;
        let (pp, keys, coms) = Atse::setup(n, t);
        let mut server_responses = vec![];
        for i in 0..n {
            let (stmt, proof) = Atse::encrypt_server(&pp, &keys[i], &coms[i]);
            server_responses.push((stmt, proof));
        }
        Atse::encrypt_client(1, &server_responses);
    }

    #[test]
    fn test_correctness_enc_nizk() {
        let mut rng = thread_rng();

        let α1 = Scalar::random(&mut rng);
        let α2 = Scalar::random(&mut rng);
        let witness = AtseNizkWitness { α1, α2 };

        let pp = AtseNizkProofParams::new();
        let h_of_x = utils::hash_to_g1(&[0; 32]);
        let h_of_x_pow_α1 = h_of_x.mul(&α1);
        let com = utils::pedersen_commit_in_g1(&pp.g, &pp.h, &α1, &α2);
        let stmt = AtseEncNizkStatement {
            g: pp.g.clone(),
            h: pp.h.clone(),
            h_of_x: h_of_x,
            h_of_x_pow_a: h_of_x_pow_α1,
            com: com
        };
        let proof = AtseEncNizkProof::prove(&witness, &stmt);
        let check = AtseEncNizkProof::verify(&stmt, &proof);
        assert!(check);
    }

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
}
