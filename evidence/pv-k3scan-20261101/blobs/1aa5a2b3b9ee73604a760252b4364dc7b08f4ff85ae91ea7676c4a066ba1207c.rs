//! Native differential and no-stub bounded source checks for the owned serializer.
use aspis_core::field::M31;
use aspis_statement::pool_v1::{
    pair_forest_semantic_terminal::r0::Public,
    pair_terminal::PoolV1PairVerifiedAfterstateV1,
    pair_tree_profile::{PoolV1PairLiveSnapshotV1, PoolV1PairLatePublicStatementV1},
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
};
use crate::reference226::{Source, public_bytes};

#[cfg(kani)]
fn digest() -> [M31; 8] {
    let x: [u32; 8] = kani::any();
    x.map(M31)
}
#[cfg(kani)]
fn arbitrary_source(withdrawal: bool) -> Source {
    let t = PoolV1PairLatePublicStatementV1 {
        live_snapshot: PoolV1PairLiveSnapshotV1 {
            pool: kani::any(), deployment_domain: kani::any(), sequence: kani::any(),
            next_pair_index: kani::any(), current_root: digest(),
            frontier: core::array::from_fn(|_| digest()),
        },
        candidate_afterstate: PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: kani::any(), next_root: digest(),
            next_frontier: core::array::from_fn(|_| digest()),
        },
    };
    if withdrawal {
        Source::Withdrawal(PoolV1WithdrawalPublicV1 {
            pool: kani::any(), deployment_domain: kani::any(), anchor_sequence: kani::any(),
            anchor_root: digest(), nullifier: digest(), asset_id: M31(kani::any()),
            amount: kani::any(), destination_token_account: kani::any(), change_commitment: digest(),
        }, t)
    } else {
        Source::Transfer(PoolV1PrivateTransferPublicV1 {
            pool: kani::any(), deployment_domain: kani::any(), anchor_sequence: kani::any(),
            anchor_root: digest(), nullifier: digest(), asset_id: M31(kani::any()),
            recipient_commitment: digest(), change_commitment: digest(),
        }, t)
    }
}

#[cfg(kani)]
fn check(source: Source) { check_controlled(source,false); }
#[cfg(kani)]
fn check_controlled(source: Source, wrong_byte: bool) {
    let actual = match source {
        Source::Transfer(p, t) => Public::Transfer(&p, &t).public_bytes(),
        Source::Withdrawal(p, t) => Public::Withdrawal(&p, &t).public_bytes(),
    };
    let expected = public_bytes(source);
    match (actual, expected) {
        (Ok(bytes), Ok((chunks, n))) => {
            assert_eq!(bytes.len(), n);
            assert!(n == 1427 || n == 1455);
            let index: u16 = kani::any();
            let i = usize::from(index);
            kani::assume(i < n);
            if wrong_byte {
                assert_eq!(bytes[i], chunks[i / 64][i % 64] ^ 1, "matched wrong-byte control");
            } else {
                assert_eq!(bytes[i], chunks[i / 64][i % 64]);
            }
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        _ => assert!(false, "complete Result mismatch"),
    }
}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(65)]
fn transfer() { check(arbitrary_source(false)); }
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(65)]
fn withdrawal() { check(arbitrary_source(true)); }

#[cfg(test)]
fn fixture(withdrawal: bool) -> Source {
    let words = |seed: u32| core::array::from_fn(|i| M31(seed + i as u32));
    let t = PoolV1PairLatePublicStatementV1 {
        live_snapshot: PoolV1PairLiveSnapshotV1 {
            pool: [7;32], deployment_domain: [11;32], sequence: 17,
            next_pair_index: 0x0123_4567_89ab_cdef,
            current_root: words(23), frontier: core::array::from_fn(|i| words(100 + 8*i as u32)),
        },
        candidate_afterstate: PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: 31, next_root: words(37),
            next_frontier: core::array::from_fn(|i| words(300 + 8*i as u32)),
        },
    };
    if withdrawal {
        Source::Withdrawal(PoolV1WithdrawalPublicV1 {
            pool: [41;32], deployment_domain: [43;32], anchor_sequence: 47,
            anchor_root: words(53), nullifier: words(61), asset_id: M31(67),
            amount: 71, destination_token_account: [73;32], change_commitment: words(79),
        },t)
    } else {
        Source::Transfer(PoolV1PrivateTransferPublicV1 {
            pool: [83;32], deployment_domain: [89;32], anchor_sequence: 97,
            anchor_root: words(101), nullifier: words(109), asset_id: M31(127),
            recipient_commitment: words(131), change_commitment: words(139),
        },t)
    }
}
#[cfg(test)]
fn finite(source: Source) {
    let native = match source {
        Source::Transfer(p,t) => Public::Transfer(&p,&t).public_bytes(),
        Source::Withdrawal(p,t) => Public::Withdrawal(&p,&t).public_bytes(),
    };
    let reference = public_bytes(source).map(|(chunks,n)| {
        let mut v=Vec::new();
        for i in 0..n { v.push(chunks[i/64][i%64]); }
        v
    });
    assert_eq!(native,reference);
}
#[test]
fn same_input_finite226() {
    for withdrawal in [false,true] {
        let p=fixture(withdrawal); finite(p);
        let bad=match p {
            Source::Transfer(mut p,t) => {p.asset_id=M31(u32::MAX); Source::Transfer(p,t)},
            Source::Withdrawal(mut p,t) => {p.amount=u32::MAX; Source::Withdrawal(p,t)},
        }; finite(bad);
    }
}

// Same fixtures as PV_B3P_Fidelity226, to audit all emitted mutable writes.
#[test]
fn emission_fixture226() {
    for withdrawal in [false,true] {
        let source=fixture(withdrawal);
        let bytes=match source {
            Source::Transfer(p,t) => Public::Transfer(&p,&t).public_bytes(),
            Source::Withdrawal(p,t) => Public::Withdrawal(&p,&t).public_bytes(),
        }.unwrap();
        println!("{}=({}, {:?})",if withdrawal {"WITHDRAWAL"} else {"TRANSFER"},bytes.len(),bytes);
        let bad=match source {
            Source::Transfer(mut p,t) => {p.asset_id=M31(u32::MAX); Source::Transfer(p,t)},
            Source::Withdrawal(mut p,t) => {p.amount=u32::MAX; Source::Withdrawal(p,t)},
        };
        let error=match bad {
            Source::Transfer(p,t) => Public::Transfer(&p,&t).public_bytes(),
            Source::Withdrawal(p,t) => Public::Withdrawal(&p,&t).public_bytes(),
        };
        assert_eq!(error,Err(aspis_core::state_only_prefix::r0::Error::Public));
        println!("{}=ERR",if withdrawal {"BAD_WITHDRAWAL"} else {"BAD_TRANSFER"});
    }
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(2049)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn both_variants() { check(arbitrary_source(kani::any())); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(2049)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn both_variants_wrong_byte() { check_controlled(arbitrary_source(kani::any()),true); }

#[cfg(test)]
#[path="owned226.rs"]
mod owned226;
#[cfg(test)]
fn finite_structural(source: Source) {
 let actual=match source {
  Source::Transfer(p,t)=>Public::Transfer(&p,&t).public_bytes(),
  Source::Withdrawal(p,t)=>Public::Withdrawal(&p,&t).public_bytes(),
 };
 let copy=match source {
  Source::Transfer(p,t)=>owned226::Public::Transfer(&p,&t).public_bytes(),
  Source::Withdrawal(p,t)=>owned226::Public::Withdrawal(&p,&t).public_bytes(),
 };
 let reference=public_bytes(source).map(|(chunks,n)|chunks.into_iter().flatten().take(n).collect::<Vec<_>>());
 assert_eq!(actual,copy);
 assert_eq!(copy,reference);
}
#[cfg(test)]
fn mutated(source: Source,region: usize,index: usize,value: u32) -> Source {
 match source {
  Source::Transfer(mut p,mut t)=> {
   match region {
    0=>p.anchor_root[index]=M31(value),1=>p.nullifier[index]=M31(value),
    2=>p.asset_id=M31(value),3=>p.recipient_commitment[index]=M31(value),
    4=>p.change_commitment[index]=M31(value),
    6=>t.live_snapshot.frontier[index/8][index%8]=M31(value),
    7=>t.candidate_afterstate.next_root[index]=M31(value),
    8=>t.candidate_afterstate.next_frontier[index/8][index%8]=M31(value),
    _=>panic!("invalid transfer region"),
   }
   Source::Transfer(p,t)
  },
  Source::Withdrawal(mut p,mut t)=> {
   match region {
    0=>p.anchor_root[index]=M31(value),1=>p.nullifier[index]=M31(value),
    2=>p.asset_id=M31(value),4=>p.change_commitment[index]=M31(value),5=>p.amount=value,
    6=>t.live_snapshot.frontier[index/8][index%8]=M31(value),
    7=>t.candidate_afterstate.next_root[index]=M31(value),
    8=>t.candidate_afterstate.next_frontier[index/8][index%8]=M31(value),
    _=>panic!("invalid withdrawal region"),
   }
   Source::Withdrawal(p,t)
  },
 }
}
#[test]
fn structural_source226() {
 let mut comparisons=0;
 for withdrawal in [false,true] {
  let base=fixture(withdrawal);
  finite_structural(base);comparisons+=1;
  for region in 0..9 {
   if (withdrawal && region==3) || (!withdrawal && region==5) {continue;}
   let n=if region==2 || region==5 {1} else if region==6 || region==8 {160} else {8};
   for index in 0..n {
    for value in [0,2147483646,2147483647,u32::MAX] {
     finite_structural(mutated(base,region,index,value));comparisons+=1;
    }
   }
  }
  for index in [0,u64::MAX,0x0123456789abcdef,1,256,65536,16777216,1u64<<32,1u64<<40,1u64<<48,1u64<<56] {
   let p=match base {
    Source::Transfer(p,mut t)=>{t.live_snapshot.next_pair_index=index;Source::Transfer(p,t)},
    Source::Withdrawal(p,mut t)=>{t.live_snapshot.next_pair_index=index;Source::Withdrawal(p,t)},
   };
   finite_structural(p);comparisons+=1;
  }
 }
 assert_eq!(comparisons,2884);
 println!("same-input structural serializer differentials: {comparisons}; finite validation");
}
