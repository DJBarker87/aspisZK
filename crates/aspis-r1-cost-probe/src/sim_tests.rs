//! G-sim tests (cfg(test), feature `r1p-check`).
use super::*;
use crate::host_commitment::EncodingDomain;
use aspis_prover::r0_fixture;

fn rand_e(state:&mut u64)->E {
    let mut m=||{*state=state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);M31(((*state>>33)%0x7fff_ffff) as u32)};
    E::new(K{c0:CM31::new(m(),m()),c1:CM31::new(m(),m())},K{c0:CM31::new(m(),m()),c1:CM31::new(m(),m())})
}

/// The one-index evaluators equal the prover's full-domain encoder.
#[test]
fn single_index_evaluation_matches_the_encoding_domain() {
    let domain=EncodingDomain::new().unwrap();
    let mut st=7u64;
    let q1:Vec<E>=(0..256).map(|_|rand_e(&mut st)).collect();
    let full=domain.evaluate(&q1,0).unwrap();
    let msg:[E;1024]=core::array::from_fn(|_|rand_e(&mut st));
    let base=msg.map(|x|M31(x.to_limbs()[0]));
    let word=domain.encode(&base).unwrap();
    let ext=msg.map(|x|x.c0());
    let wext=domain.encode(&ext).unwrap();
    for u in [0usize,1,2,3,4,5,77,1023,4096,65535,65536,131071,200003,262143] {
        assert_eq!(eval_at(&q1,u),full[u],"fold word index {u}");
        assert_eq!(encode_at(&base,u),core::array::from_fn::<_,4,_>(|s|word[4*u+s]),"base fibre {u}");
        assert_eq!(encode_at(&ext,u),core::array::from_fn::<_,4,_>(|s|wext[4*u+s]),"ext fibre {u}");
    }
}

/// simE's proof, from the public statement alone, passes the strict
/// two-transaction verifier and the dense verifier under the programmed
/// oracle; every programmed address is read by the verifier; the same bytes
/// fail under the unprogrammed hash.
#[test]
fn simulated_proof_verifies_under_the_programmed_oracle() {
    let fixture=r0_fixture::prepare(false);
    let public=fixture.public();
    let sim=sim_e(public,[0x5a;32]).expect("simulated view");
    assert_eq!(sim.transcript_reads,115);
    let (ok,programmed,read)=verify_programmed(public,&sim.proof,sim.table.clone());
    assert_eq!(ok,Ok(()));
    assert_eq!(programmed,sim.table.len());
    assert_eq!(read,programmed,"the VerLog is exactly the verifier's programmed reads");
    let public_bytes=public.public_bytes().unwrap();
    assert!(crate::verifier::tx1(public,&public_bytes,&sim.proof,11,LegacyHashFn(HOST_HASH),None).is_err(),"unprogrammed oracle rejects");
}

/// Teeth: without S₀ in the mask-sum cell, or without the round-9 shift Ψ_ch,
/// the (consistently programmed) view is rejected.
#[test]
fn reference_point_ingredients_are_necessary() {
    let fixture=r0_fixture::prepare(false);
    let public=fixture.public();
    for ablation in [Ablation::NoS0,Ablation::NoShift] {
        let sim=sim_e_ablated(public,[0x5a;32],ablation).expect("ablated view");
        let (ok,_,_)=verify_programmed(public,&sim.proof,sim.table);
        assert!(ok.is_err(),"{ablation:?} must be rejected");
    }
}
