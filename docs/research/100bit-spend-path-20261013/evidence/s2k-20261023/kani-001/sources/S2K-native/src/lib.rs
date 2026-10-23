#![cfg(kani)]
#![allow(non_snake_case)]
use aspis_statement::{pool_v1::*, encode_digest_canonical, poseidon2::Digest};
use aspis_core::field::{M31,P};
mod statement;
include!("S2K_construct.rs");
include!("S2K_frontier_step.rs");
mod validator_parent {
    pub use aspis_statement::pool_v1::POOL_V1_PAIR_CAPACITY;
    pub mod pair_tree_profile {
        use aspis_statement::poseidon2::Digest;
        use aspis_core::field::P;
        include!("S2K_canonical.rs");
    }
    pub mod inner {
        use aspis_statement::pool_v1::*;
        include!("S2K_validate.rs");
        pub fn run(a: &PoolV1PairVerifiedAfterstateV1) -> Result<(),PoolV1PairVerifierTransportErrorV1> {
            validate_verified_afterstate(a)
        }
    }
}
fn digest() -> Digest { core::array::from_fn(|_| M31(kani::any())) }

#[kani::proof]
#[kani::unwind(34)]
fn S2K_construct_exact() {
    let s=statement::statement();
    let r=construct(&s);
    assert_eq!(r.transition_kind,s.transition_kind());
    assert_eq!(r.master_account,s.common().master_account);
    assert_eq!(r.selected_lane_account,s.common().selected_lane_account);
    assert_eq!(r.output_lane,s.common().output_lane);
    assert_eq!(r.nullifier,*s.nullifier());
    assert_eq!(r.verified_afterstate,s.common().lane_transition.candidate_afterstate);
    kani::cover!(s.transition_kind()==PoolV1TransitionKind::PrivateTransfer);
    kani::cover!(s.transition_kind()==PoolV1TransitionKind::Withdrawal);
}

#[kani::proof]
#[kani::unwind(34)]
fn S2K_digest_byte() {
    let d=digest();
    let i:usize=kani::any();kani::assume(i<32);
    let bytes=encode_digest_canonical(&d);
    assert_eq!(bytes[i], (d[i/4].0 >> (8*(i%4))) as u8);
    kani::cover!(i==0);kani::cover!(i==31);
}

#[kani::proof]
#[kani::unwind(34)]
fn S2K_afterstate_validation() {
    let a=PoolV1PairVerifiedAfterstateV1 {
        next_pair_index:kani::any(),next_root:digest(),
        next_frontier:core::array::from_fn(|_|digest()),
    };
    let mut canonical=true;
    for i in 0..8 { canonical &= a.next_root[i].0<P; }
    for i in 0..20 { for j in 0..8 { canonical &= a.next_frontier[i][j].0<P; } }
    let expected=if a.next_pair_index==0 || a.next_pair_index>POOL_V1_PAIR_CAPACITY {
        Err(PoolV1PairVerifierTransportErrorV1::InvalidAfterstateIndex)
    } else if !canonical {
        Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)
    } else { Ok(()) };
    assert_eq!(validator_parent::inner::run(&a),expected);
    kani::cover!(expected.is_ok());
    kani::cover!(expected==Err(PoolV1PairVerifierTransportErrorV1::InvalidAfterstateIndex));
    kani::cover!(expected==Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate));
}

#[kani::proof]
#[kani::unwind(690)]
fn S2K_frontier_iteration() {
    let before:[u8;688]=core::array::from_fn(|_|kani::any());
    let node=digest();let level:usize=kani::any();kani::assume(level<20);
    let i:usize=kani::any();kani::assume(i<688);
    let after=frontier_step(before,level,&node);
    let start=48+32*level;
    if start<=i && i<start+32 {
        let j=i-start;
        assert_eq!(after[i], (node[j/4].0 >> (8*(j%4))) as u8);
    } else { assert_eq!(after[i],before[i]); }
    kani::cover!(level==0 && i==48);
    kani::cover!(level==19 && i==687);
}
