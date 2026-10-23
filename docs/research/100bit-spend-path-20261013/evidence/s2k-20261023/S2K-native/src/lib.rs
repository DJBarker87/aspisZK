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

// Split replacement for kani004: direct Arbitrary buffer avoids the 688-step
// from_fn initializer. Callee source statements are unchanged; selected write
// and outside-region frame are checked separately.
#[kani::proof]
#[kani::unwind(34)]
fn S2K_frontier_written_byte() {
    let before:[u8;688]=kani::any();
    let node=digest();let level:usize=kani::any();kani::assume(level<20);
    let j:usize=kani::any();kani::assume(j<32);
    let after=frontier_step(before,level,&node);
    assert_eq!(after[48+32*level+j],(node[j/4].0 >> (8*(j%4))) as u8);
    kani::cover!(level==0 && j==0);
    kani::cover!(level==19 && j==31);
}

#[kani::proof]
#[kani::unwind(34)]
fn S2K_frontier_other_byte() {
    let before:[u8;688]=kani::any();
    let node=digest();let level:usize=kani::any();kani::assume(level<20);
    let i:usize=kani::any();kani::assume(i<688);
    let start=48+32*level;kani::assume(i<start || i>=start+32);
    let after=frontier_step(before,level,&node);
    assert_eq!(after[i],before[i]);
    kani::cover!(i==0 && level==19);
    kani::cover!(i==687 && level==0);
}

// Terminal isolation of kani005: fixed-size destination only. This does NOT
// port the original indexed &mut output[start..start+32] to this destination.
#[kani::proof]
#[kani::unwind(34)]
fn S2K_fixed_digest_copy() {
    let mut output:[u8;32]=kani::any();
    let node=digest();let j:usize=kani::any();kani::assume(j<32);
    output.copy_from_slice(&encode_digest_canonical(&node));
    assert_eq!(output[j],(node[j/4].0 >> (8*(j%4))) as u8);
    kani::cover!(j==0);kani::cover!(j==31);
}

#[kani::proof]
fn S2K_frontier_bounds() {
    let level:usize=kani::any();kani::assume(level<20);
    let start=48+32*level;
    assert!(48<=start);
    assert!(start+32<=688);
    let j:usize=kani::any();kani::assume(j<32);
    assert!(start+j<688);
    assert_eq!((start+j-start)/4,j/4);
    assert_eq!((start+j-start)%4,j%4);
    kani::cover!(level==0 && j==0);
    kani::cover!(level==19 && j==31);
}

include!("S2K_concrete.rs");

include!("S2K_result_validate.rs");

// One result-validation child, not an enclosing emitter harness.
#[kani::proof]
#[kani::unwind(34)]
fn S2K_result_validation_step() {
    let statement=statement::statement();
    let result=construct(&statement);
    let expected=if result.master_account==[0;32] || result.selected_lane_account==[0;32] {
        Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)
    } else {
        match pool_v1_pair_forest_output_lane_v1(&result.nullifier) {
            Err(e)=>Err(PoolV1PairForestTerminalFormatErrorV1::Account(e)),
            Ok(lane) if lane!=result.output_lane=>Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch),
            Ok(_)=>validator_parent::inner::run(&result.verified_afterstate)
                .map_err(PoolV1PairForestTerminalFormatErrorV1::Afterstate),
        }
    };
    assert_eq!(validate_result(&result),expected);
    kani::cover!(expected.is_ok());
}

// The remaining SAME-statement admission cut: no whole emit call and no
// full result re-encoding. Actual statement validation must supply the
// antecedents of kani031 on the constructor's SAME candidate afterstate.
#[kani::proof]
#[kani::unwind(34)]
fn S2K_statement_result_admission() {
    let statement=statement::statement();
    let valid=validate_pool_v1_pair_forest_terminal_statement_v1(&statement);
    if valid.is_ok() {
        let result=construct(&statement);
        assert!(result.master_account!=[0;32]);
        assert!(result.selected_lane_account!=[0;32]);
        assert_eq!(pool_v1_pair_forest_output_lane_v1(&result.nullifier),Ok(result.output_lane));
        assert_eq!(validator_parent::inner::run(&result.verified_afterstate),Ok(()));
    }
    kani::cover!(valid.is_ok() && statement.transition_kind()==PoolV1TransitionKind::PrivateTransfer);
    kani::cover!(valid.is_ok() && statement.transition_kind()==PoolV1TransitionKind::Withdrawal);
}

// Isolation of kani032: just the native lane-transition encoder and the
// candidate-afterstate consequence; no payment, common bindings, or result.
#[kani::proof]
#[kani::unwind(34)]
fn S2K_late_afterstate_admission() {
    let statement=statement::statement().common().lane_transition;
    let mut bytes=[0;POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES];
    let valid=encode_pool_v1_pair_late_public_statement_v1(&statement,&mut bytes);
    if valid.is_ok() {
        assert_eq!(validator_parent::inner::run(&statement.candidate_afterstate),Ok(()));
    }
    kani::cover!(valid.is_ok());
}

include!("S2K_status_contract.rs");

include!("S2K_fields.rs");

// Actual iterator value/schedule, separated from encoding and buffer writes.
#[kani::proof]
#[kani::unwind(22)]
fn S2K_frontier_iterator_value() {
    let rows:[Digest;20]=core::array::from_fn(|_|digest());
    let selected:usize=kani::any(); kani::assume(selected<20);
    let word:usize=kani::any(); kani::assume(word<8);
    let mut iter=rows.iter().enumerate();
    for k in 0..20 {
        let (level,node)=iter.next().unwrap();
        assert_eq!(level,k);
        if k==selected { assert_eq!(node[word].0,rows[selected][word].0); }
    }
    assert!(iter.next().is_none());
    kani::cover!(selected==0 && word==0);
    kani::cover!(selected==19 && word==7);
}

// Result encoder's one688-byte sub-encoder copy, independently specialized
// from S2G's1768-byte contract. Not a whole result/emitter harness.
#[kani::requires(destination.len() == 688 && source.len() == 688)]
#[kani::requires(observed < 688)]
#[kani::requires(expected == source[observed])]
#[kani::modifies(destination.as_mut_ptr().cast::<[u8;688]>())]
#[kani::ensures(|_| destination[observed] == expected)]
pub fn S2K_copy688(destination: &mut [u8], source: &[u8], observed: usize, expected: u8) {
    destination.copy_from_slice(source);
}
#[kani::proof_for_contract(S2K_copy688)]
#[kani::unwind(34)]
fn S2K_copy688_contract() {
    let mut destination:[u8;688]=kani::any();
    let source:[u8;688]=kani::any();
    let observed:usize=kani::any(); kani::assume(observed<688);
    S2K_copy688(&mut destination,&source,observed,source[observed]);
    kani::cover!(observed==0); kani::cover!(observed==687);
}

include!("S2K_result_fields.rs");

include!("S2K_admission.rs");

// Same-signature small-copy contract for the afterstate encoder's actual
// 4/8/32-byte calls. The modifies target is the typed mutable slice itself;
// no oversized raw-pointer region or fabricated pointer identity is used.
#[kani::requires(destination.len() == source.len())]
#[kani::requires(matches!(source.len(),4|8|32))]
#[kani::modifies(destination)]
#[kani::ensures(|_| destination == source)]
fn S2K_copy_small(destination: &mut [u8], source: &[u8]) {
    destination.copy_from_slice(source);
}
#[kani::proof_for_contract(S2K_copy_small)]
#[kani::unwind(34)]
fn S2K_copy_small_contract() {
    let mut destination:[u8;32]=kani::any();
    let source:[u8;32]=kani::any();
    let width:usize=kani::any();kani::assume(matches!(width,4|8|32));
    S2K_copy_small(&mut destination[..width],&source[..width]);
    kani::cover!(width==4);kani::cover!(width==8);kani::cover!(width==32);
}


// Contract verified ONLY at T=u8; consumers below are byte-copy mono instances.
#[kani::requires(destination.len() == source.len())]
#[kani::requires(matches!(source.len(),4|8|32))]
#[kani::modifies(destination)]
#[kani::ensures(|_| destination == source)]
fn S2K_copy_small_generic<T: Copy + PartialEq + kani::Arbitrary>(destination: &mut [T], source: &[T]) {
    destination.copy_from_slice(source);
}
#[kani::proof_for_contract(S2K_copy_small_generic)]
#[kani::unwind(34)]
fn S2K_copy_small_u8_contract() {
    let mut destination:[u8;32]=kani::any();
    let source:[u8;32]=kani::any();
    let width:usize=kani::any();kani::assume(matches!(width,4|8|32));
    S2K_copy_small_generic::<u8>(&mut destination[..width],&source[..width]);
    kani::cover!(width==4);kani::cover!(width==8);kani::cover!(width==32);
}

// A single ORIGINAL source frontier iteration, now using the checked
// same-signature std-copy contract. No whole encoder/emitter is harnessed.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,S2K_copy_small_generic)]
#[kani::stub_verified(S2K_copy_small_generic)]
fn S2K_frontier_typed_slice() {
    let before:[u8;688]=kani::any();
    let node=digest();let level:usize=kani::any();kani::assume(level<20);
    let j:usize=kani::any();kani::assume(j<32);
    let i:usize=kani::any();kani::assume(i<688 && (i<48+32*level || i>=80+32*level));
    let after=frontier_step(before,level,&node);
    assert_eq!(after[48+32*level+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(after[i],before[i]);
    kani::cover!(level==0 && j==0);kani::cover!(level==19 && j==31);
}
