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
    assert_eq!(sim.proof.len(),compact::PROOF_BYTES);
    assert_eq!(&sim.proof[..8],compact::MAGIC);
    let (ok,programmed,read)=verify_programmed(public,&sim.proof,sim.table.clone());
    assert_eq!(ok,Ok(()));
    assert_eq!(programmed,sim.table.len());
    assert_eq!(programmed,sim.transcript_reads+sim.commitment_reads);
    assert_eq!(read,programmed,"the VerLog is exactly the verifier's programmed reads");
    let public_bytes=public.public_bytes().unwrap();
    assert!(crate::verifier::tx1(public,&public_bytes,&sim.proof,crate::verifier::SPLIT,LegacyHashFn(HOST_HASH),None).is_err(),"unprogrammed oracle rejects");
    assert!(crate::dense::verify(public,&sim.proof,HOST_HASH).is_err(),"real hash dense rejects");
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

/// The two transaction batches can share leaves, adjacent pairs and ancestors.
/// Assembly supplies digests only; each batch reuses the same programmed tree.
#[test]
fn binary_batches_share_consistent_programmed_nodes() {
    let table=RefCell::new((Table::new(),false));
    let mut coins=Coins::new([0x91;32],0,2);
    let leaves:BTreeMap<usize,(Vec<u8>,[u8;32])>=[0usize,1,4,6,65535].into_iter()
        .map(|i|(i,(i.to_le_bytes().to_vec(),coins.coin()))).collect();
    let root=coins.coin();
    let (tree,reads)=program_tree(&table,&mut coins,0x72,&leaves,root).unwrap();
    let (table,collision)=table.into_inner();
    assert!(!collision);
    assert_eq!(table.len(),reads);
    let before=table.len();
    let batches=[vec![0u32,1,4],vec![1,4,6,65535]];
    let nodes:Vec<_>=batches.iter().map(|ix|tree.multiproof(ix).unwrap()).collect();
    assert_eq!(table.len(),before,"assembling nodes makes no oracle calls");
    install(table);
    for (ix,nodes) in batches.iter().zip(nodes) {
        assert_eq!(nodes.len(),32*multiproof::node_count(multiproof::Arity::Two,ix).unwrap());
        let values:Vec<_>=ix.iter().map(|&i|{
            let (v,s)=&leaves[&(i as usize)];
            private_leaf_hash_with_digest(LegacyHashFn(programmed_hash),0x72,v,s)
        }).collect();
        assert!(multiproof::verify(LegacyHashFn(programmed_hash),multiproof::Arity::Two,
            &root,ix,&values,&nodes));
    }
    assert_eq!(uninstall(),(reads,reads));
}
