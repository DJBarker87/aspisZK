extern crate alloc;
use super::*;
use aspis_core::field::M31;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn encoder_reply(digest:&Digest)->[u8;32]{
 let a=digest[0].0.to_le_bytes();let b=digest[1].0.to_le_bytes();let c=digest[2].0.to_le_bytes();let d=digest[3].0.to_le_bytes();let e=digest[4].0.to_le_bytes();let f=digest[5].0.to_le_bytes();let g=digest[6].0.to_le_bytes();let h=digest[7].0.to_le_bytes();
 [a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],c[0],c[1],c[2],c[3],d[0],d[1],d[2],d[3],e[0],e[1],e[2],e[3],f[0],f[1],f[2],f[3],g[0],g[1],g[2],g[3],h[0],h[1],h[2],h[3]]
}
#[kani::proof] #[kani::unwind(512)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(crate::encode_digest_canonical,encoder_reply)]
fn marker_encoding(){
 let raw:[u32;8]=kani::any();let digest=[M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3]),M31(raw[4]),M31(raw[5]),M31(raw[6]),M31(raw[7])];
 let marker=PoolV1NullifierMarkerV1{transition_kind:PoolV1TransitionKind::PrivateTransfer,pool:[0;32],deployment_domain:[0;32],nullifier:digest,retained_anchor_sequence:0,retained_anchor_root:[M31(0);8],verifier_profile:[0;32],verifier_release:[0;32]};
 let got=marker.canonical_nullifier_encoding();let expected=encoder_reply(&digest);assert!((got==expected)!=cfg!(PCG_NEG_MARKER));
}
