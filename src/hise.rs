use bls12_381::{pairing, G1Projective, G2Projective, Scalar, Gt};
use pairing::group::{Curve, GroupEncoding};
use ff::*;
use rand::{thread_rng};
use std::{ops::{Add, Mul, Neg}};

use crate::polynomial::*;
use crate::utils;

type HiseWitnessCommitment = (G1Projective, G1Projective);

pub struct HiseNizkProofParams {
    pub g: G1Projective,
    pub h: G1Projective,
}

impl <'a> HiseNizkProofParams {
    pub fn new() -> HiseNizkProofParams {
        let mut rng = thread_rng();

        let g = G1Projective::generator();
        
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
    pub ut1: G1Projective,
    pub ut2: G1Projective,
    pub αz1: Scalar,
    pub αz2: Scalar,
}

pub struct HiseDecNizkProof {
    pub ut1: G1Projective,
    pub ut2: G1Projective,
    pub ut3: G1Projective,
    pub αz1: Scalar,
    pub αz2: Scalar,
    pub βz1: Scalar,
    pub βz2: Scalar,
}

pub struct HiseEncNizkStatement {
    pub g: G1Projective,
    pub h: G1Projective,
    pub h_of_x_eps: G1Projective, //H(x_eps)
    pub h_of_x_eps_pow_a: G1Projective, //H(x_eps)^a 
    pub com: G1Projective, //ped com g^a. h^b
}

pub struct HiseDecNizkStatement {
    pub g: G1Projective,
    pub h: G1Projective,
    pub h_of_x_eps: G1Projective, //H(x_eps)
    pub h_of_x_w: G1Projective, //H(x_eps)
    pub h_of_x_eps_pow_a_h_of_x_w_pow_b: G1Projective, //H(x_eps)^a . H(w)^b
    pub com_a: G1Projective, //ped com g^a. h^b
    pub com_b: G1Projective,
}

pub struct HiseNizkWitness {
    pub α1: Scalar,
    pub α2: Scalar,
    pub β1: Scalar,
    pub β2: Scalar,
}

impl <'a> HiseEncNizkProof {

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


impl <'a> HiseDecNizkProof {

    fn random_oracle(
        ut1: &G1Projective, 
        ut2: &G1Projective,
        ut3: &G1Projective,
    ) -> Scalar {
        let mut bytes = vec![];
    
        bytes.extend_from_slice(&ut1.to_bytes().as_ref());
        bytes.extend_from_slice(&ut2.to_bytes().as_ref());
        bytes.extend_from_slice(&ut3.to_bytes().as_ref());
    
        utils::hash_to_scalar(&bytes)
    }

    // exists α1, α2, β1, β2.  s.t. \phi(α1,α2) = true
    // \phi(α1, α2, β1, β2) := { 
    //      com_α = g^{α1}.h^{α2} ∧ 
    //      com_β = g^{β1}.h^{β2} ∧ 
    //      prfEval = H(x1)^{α1} . H(x2)^{β1} 
    // }
    pub fn prove(
        witness: &HiseNizkWitness,
        stmt: &HiseDecNizkStatement
    ) -> HiseDecNizkProof {
        let mut rng = thread_rng();
        let αt1 = Scalar::random(&mut rng);
        let αt2 = Scalar::random(&mut rng);
        let βt1 = Scalar::random(&mut rng);
        let βt2 = Scalar::random(&mut rng);

        let ut1 = stmt.h_of_x_eps.mul(αt1).add(stmt.h_of_x_w.mul(βt1));
        let ut2 = stmt.g.mul(αt1).add(stmt.h.mul(αt2));
        let ut3 = stmt.g.mul(βt1).add(stmt.h.mul(βt2));

        //TODO: this needs more inputs
        let c = HiseDecNizkProof::random_oracle(&ut1, &ut2, &ut3);

        let αz1 = αt1 + c * witness.α1;
        let αz2 = αt2 + c * witness.α2;
        let βz1 = βt1 + c * witness.β1;
        let βz2 = βt2 + c * witness.β2;

        HiseDecNizkProof { ut1, ut2, ut3, αz1, αz2, βz1, βz2 }
    }

    pub fn verify(
        stmt: &HiseDecNizkStatement,
        proof: &HiseDecNizkProof,
    ) -> bool {
        let c = HiseDecNizkProof::random_oracle(&proof.ut1, &proof.ut2, &proof.ut3);
        
        let lhs1 = stmt.h_of_x_eps.mul(&proof.αz1).add(stmt.h_of_x_w.mul(&proof.βz1));
        let rhs1 = proof.ut1.add(stmt.h_of_x_eps_pow_a_h_of_x_w_pow_b.mul(&c));

        let lhs2 = stmt.g.mul(&proof.αz1).add(stmt.h.mul(&proof.αz2));
        let rhs2 = proof.ut2.add(stmt.com_a.mul(&c));

        let lhs3 = stmt.g.mul(&proof.βz1).add(stmt.h.mul(&proof.βz2));
        let rhs3 = proof.ut3.add(stmt.com_b.mul(&c));

        return lhs1 == rhs1 && lhs2 == rhs2 && lhs3 == rhs3;
    }
}


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

            let com_α = utils::pedersen_commit_in_g1(
                &pp.g, &pp.h, &α1_i, &α2_i);
            let com_β = utils::pedersen_commit_in_g1(
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
        com: &HiseWitnessCommitment,
        γ: [u8;32] //merkle root
    ) -> (HiseEncNizkStatement, HiseEncNizkProof) {
    
        let h_of_γ = utils::hash_to_g1(&γ);   //γ comes from the client
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

    pub fn decrypt_server(
        pp: &HiseNizkProofParams, 
        key: &HiseNizkWitness,
        com: &HiseWitnessCommitment,
        x_eps: [u8;32],
        x_w: [u8;32]
    ) -> (HiseDecNizkStatement, HiseDecNizkProof) {
       
        // x_eps and x_w come from the client
        let h_of_x_eps = utils::hash_to_g1(&x_eps); 
        let h_of_x_w = utils::hash_to_g1(&x_w);

        let eval = h_of_x_eps.mul(key.α1).add(h_of_x_w.mul(key.β1));

        let stmt = HiseDecNizkStatement {
            g: pp.g.clone(),
            h: pp.h.clone(),
            h_of_x_eps: h_of_x_eps,
            h_of_x_w: h_of_x_w,
            h_of_x_eps_pow_a_h_of_x_w_pow_b: eval.clone(),
            com_a: com.0.clone(),
            com_b: com.1.clone()
        };

        let proof = HiseDecNizkProof::prove(key, &stmt);
        return (stmt, proof);
    }

    //Phase 1 of encryption: Client sends a merkle data commitment to the servers.
    //For simplicity a random commitment is taken.
    
    pub fn encrypt_client_phase_1() -> [u8;32] {
        let mut γ = Hise::get_random_data_commitment();
        return γ;
    }

    //Phase 2 of encryption: Client receives the partial evlatuations from the servers.
    //These evaluations are aggregated to eventually generate message specific keys and ultimately the ciphertexts.

    pub fn encrypt_client_phase_2(
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
        let solo_evals: Vec<G1Projective> = server_responses.
            iter().
            map(|(s,p)| s.h_of_x_eps_pow_a.clone()).
            collect();

        //this is called z in the paper
        let gk = utils::multi_exp_g1(solo_evals.as_slice(), &coeffs.as_slice()[0..n]);
        // credit chatgpt: This function takes a floating-point number x as input and 
        // returns the logarithm base 2 of x, rounded up to the nearest integer. 
        let log_m = (m as f64).log2().ceil() as u64;

        //for each of the m ciphertexts, we need to do log m work
        let mut rng = thread_rng();
        let g2 = G2Projective::generator();
        for i in 0..m {
            let r_i = Scalar::random(&mut rng);
            let g1_pow_r_i = g2.mul(&r_i);
            
            for j in 0..log_m {
                let x_w_j = Hise::get_random_data_commitment(); 
                let h_of_x_w_j = utils::hash_to_g1(x_w_j.as_slice());
                let h_of_x_w_j_pow_r_i = h_of_x_w_j.mul(&r_i);
            }

            let mk_j = pairing(&gk.to_affine(), &g1_pow_r_i.to_affine());
        }
    }

    //Phase 1 of decryption: Client sends the values x_eps and x_w to the servers
    // The values x_eps and x_w correspond to hash values at the root and at the node with path w.
    //For simplicity random commitments are taken.

    pub fn decrypt_client_phase_1() -> ([u8;32], [u8;32]){
        let x_eps = Hise::get_random_data_commitment();
        let x_w = Hise::get_random_data_commitment();
        return (x_eps, x_w);
    }

    pub fn decrypt_client_phase_2(
        m: usize, //number of messages
        server_responses: &Vec<(HiseDecNizkStatement, HiseDecNizkProof)>) {
        //first verify all the proofs
        for (stmt, proof) in server_responses {
            assert!(HiseDecNizkProof::verify(stmt, proof));
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
            map(|(s,p)| s.h_of_x_eps_pow_a_h_of_x_w_pow_b.clone()).
            collect();

        let gk = utils::multi_exp_g1(solo_evals.as_slice(), &coeffs.as_slice()[0..n]);

        let mut rng = thread_rng();
        let R = G2Projective::generator().mul(&Scalar::random(&mut rng));
        let S_w = G2Projective::generator().mul(&Scalar::random(&mut rng));
        let g_B = server_responses[0].0.com_b;
        for i in 0..m {
            //compute e(R,z) . e(g^B, S_w)^-1
            let e_r_z = pairing(&gk.to_affine(), &R.to_affine());
            let e_g_B_s_w = pairing(&g_B.to_affine(), &S_w.to_affine());
            let _ = e_r_z.add(e_g_B_s_w.neg());
        }
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
        // t = n/3: 2, 4, 6, 8
        let rows = [[2,4,6,8], [3,6,9,12], [4,8,12,16]];
        for row in rows.iter() {
            for t in row.iter() {
                let t = *t as usize; let n = t;

                let mut durations = vec![];
                let mut γ = Hise::encrypt_client_phase_1();

                for m in [1, 100, 10000].iter() {
                    let m = *m as usize;

                    let (pp, keys, coms) = Hise::setup(n, t);

                    let mut server_responses = vec![];
                    for i in 0..n {
                        let (stmt, proof) = Hise::encrypt_server(&pp, &keys[i], &coms[i], γ);
                        server_responses.push((stmt, proof));
                    }
            
                    let now = Instant::now();
                    let _ = Hise::encrypt_server(&pp, &keys[0], &coms[0], γ);
                    Hise::encrypt_client_phase_2(m, &server_responses);
                    let duration = now.elapsed();
                    println!("ATSE encrypt for {} nodes and {} messages: {} seconds",
                            t, m, duration.as_secs_f32());
                    durations.push(duration.as_secs_f32());
                }
                print!("t = {}: ", t);
                for duration in durations.iter() {
                    print!("{:.3} & ", duration);
                }
                print!("\n");
            }
        }
    }

    #[test]
    fn test_dec_latency() {
        // n = 6,12,18.24
        // t = n/3: 2, 4, 6, 8
        let rows = [[2,4,6,8], [3,6,9,12], [4,8,12,16]];
        for row in rows.iter() {
            for t in row.iter() {
                let t = *t as usize; let n = t;

                let mut durations = vec![];
                for m in [1, 100, 10000].iter() {
                    let m = *m as usize;

                    let (pp, keys, coms) = Hise::setup(n, t);

                    let mut server_responses = vec![];
                    let (mut x_eps, mut x_w) = Hise::decrypt_client_phase_1();

                    for i in 0..n {
                        let (stmt, proof) = Hise::decrypt_server(&pp, &keys[i], &coms[i], x_eps, x_w);
                        server_responses.push((stmt, proof));
                    }
            
                    let now = Instant::now();
                    let _ = Hise::decrypt_server(&pp, &keys[0], &coms[0], x_eps, x_w);
                    Hise::decrypt_client_phase_2(m, &server_responses);
                    let duration = now.elapsed();
                    println!("HiSE decrypt for {} nodes and {} messages: {} seconds",
                            t, m, duration.as_secs_f32());
                    durations.push(duration.as_secs_f32());
                }
                print!("t = {}: ", t);
                for duration in durations.iter() {
                    print!("{:.3} & ", duration);
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

                    let (pp, keys, coms) = Hise::setup(n, t);

                    let mut server_responses = vec![];
                    let mut γ = Hise::encrypt_client_phase_1();

                    for i in 0..n {
                        let (stmt, proof) = Hise::encrypt_server(&pp, &keys[i], &coms[i], γ);
                        server_responses.push((stmt, proof));
                    }
            
                    let now = Instant::now();
                    Hise::encrypt_client_phase_2(m, &server_responses);
                    let duration = now.elapsed().as_secs_f32();
                    let throughput = (num_cpu as f32) * ((m as f32) / duration);
                    println!("HISE throughput for {} nodes and {} messages: {} seconds; {} enc/sec",
                            t, m, duration, throughput);
                    measurements.push(throughput);
                }
                print!("t = {}: ", t);
                for throughput in measurements.iter() {
                    print!("{:.2} & ", throughput);
                }
                print!("\n");
            }
        }
    }

    #[test]
    fn test_dec_throughput() {
        let num_cpu = 16;
        let rows = [[2,4,6,8], [3,6,9,12], [4,8,12,16]];
        for row in rows.iter() {
            for t in row.iter() {
                let t = *t as usize; let n = t;

                let mut measurements = vec![];
                for m in [1, 100, 10000].iter() {
                    let m = *m as usize;

                    let (pp, keys, coms) = Hise::setup(n, t);

                    let mut server_responses = vec![];
                    let (mut x_eps, mut x_w) = Hise::decrypt_client_phase_1();

                    for i in 0..n {
                        let (stmt, proof) = Hise::decrypt_server(&pp, &keys[i], &coms[i], x_eps, x_w);
                        server_responses.push((stmt, proof));
                    }
            
                    let now = Instant::now();
                    Hise::decrypt_client_phase_2(m, &server_responses);
                    let duration = now.elapsed().as_secs_f32();
                    let throughput = (num_cpu as f32) * ((m as f32) / duration);
                    println!("HISE throughput for {} nodes and {} messages: {} seconds; {} enc/sec",
                            t, m, duration, throughput);
                    measurements.push(throughput);
                }
                print!("t = {}: ", t);
                for throughput in measurements.iter() {
                    print!("{:.2} & ", throughput);
                }
                print!("\n");
            }
        }
    }


    #[test]
    fn test_correctness_enc_nizk() {
        let mut rng = thread_rng();

        let α1 = Scalar::random(&mut rng);
        let α2 = Scalar::random(&mut rng);
        let β1 = Scalar::random(&mut rng);
        let β2 = Scalar::random(&mut rng);
        let witness = HiseNizkWitness { α1, α2, β1, β2 };

        let pp = HiseNizkProofParams::new();
        let h_of_x_eps = utils::hash_to_g1(&[0; 32]);
        let stmt = HiseEncNizkStatement {
            g: pp.g.clone(),
            h: pp.h.clone(),
            h_of_x_eps: h_of_x_eps,
            h_of_x_eps_pow_a: h_of_x_eps.mul(&α1),
            com: utils::pedersen_commit_in_g1(&pp.g, &pp.h, &α1, &α2)
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
