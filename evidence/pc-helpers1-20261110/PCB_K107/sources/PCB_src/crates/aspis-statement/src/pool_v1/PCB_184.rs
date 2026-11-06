use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn encode_spec(root:&Digest)->[u8;32] {
    let w0=root[0].0.to_le_bytes();
    let w1=root[1].0.to_le_bytes();
    let w2=root[2].0.to_le_bytes();
    let w3=root[3].0.to_le_bytes();
    let w4=root[4].0.to_le_bytes();
    let w5=root[5].0.to_le_bytes();
    let w6=root[6].0.to_le_bytes();
    let w7=root[7].0.to_le_bytes();
    [w0[0], w0[1], w0[2], w0[3], w1[0], w1[1], w1[2], w1[3], w2[0], w2[1], w2[2], w2[3], w3[0], w3[1], w3[2], w3[3], w4[0], w4[1], w4[2], w4[3], w5[0], w5[1], w5[2], w5[3], w6[0], w6[1], w6[2], w6[3], w7[0], w7[1], w7[2], w7[3]]
}

pub(super) fn reference(x:PoolV1NullifierMarkerV1)->[u8;32] {encode_spec(&x.nullifier)}
fn encoder_reply(d:&Digest)->[u8;32] {let out:[u8;32]=kani::any();kani::assume(out==encode_spec(d));out}
fn marker()->PoolV1NullifierMarkerV1 {PoolV1NullifierMarkerV1 {transition_kind:if kani::any(){PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal},pool:kani::any(),deployment_domain:kani::any(),nullifier:kani::any(),retained_anchor_sequence:kani::any(),retained_anchor_root:kani::any(),verifier_profile:kani::any(),verifier_release:kani::any()}}
#[kani::proof_for_contract(PoolV1NullifierMarkerV1::canonical_nullifier_encoding)]
#[kani::stub(crate::encode_digest_canonical,encoder_reply)]
#[kani::unwind(34)] fn contract(){let x=marker();let _=x.canonical_nullifier_encoding();}
#[kani::ensures(|r|r[0]==x[0])]fn weak(x:[u8;32])->[u8;32] {x}
#[kani::proof_for_contract(weak)]#[kani::unwind(34)]fn weak_contract(){let _=weak(kani::any());}
#[kani::proof]#[kani::unwind(34)]fn real(){let x:[u8;32]=kani::any();assert_eq!(weak(x)[1],x[1]);}
#[kani::proof]#[kani::stub_verified(weak)]#[kani::unwind(34)]fn unimplied(){let x:[u8;32]=kani::any();assert_eq!(weak(x)[1],x[1]);}
#[kani::modifies(&mut x[0])]#[kani::ensures(|_|true)]fn bad_frame(x:&mut [u8;2])->[u8;32] {x[1]=x[1].wrapping_add(1);[0;32]}
#[kani::proof_for_contract(bad_frame)]#[kani::unwind(34)]fn frame(){let mut x:[u8;2]=kani::any();let _=bad_frame(&mut x);}
#[kani::proof]#[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<32);dst.copy_from_slice(&src);assert_ne!(dst[i],src[i]);}
