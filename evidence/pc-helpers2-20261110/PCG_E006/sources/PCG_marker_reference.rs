pub fn encode(digest:[u32;8])->[u8;32]{
let a=digest[0].to_le_bytes();
let b=digest[1].to_le_bytes();
let c=digest[2].to_le_bytes();
let d=digest[3].to_le_bytes();
let e=digest[4].to_le_bytes();
let f=digest[5].to_le_bytes();
let g=digest[6].to_le_bytes();
let h=digest[7].to_le_bytes();
[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],c[0],c[1],c[2],c[3],d[0],d[1],d[2],d[3],e[0],e[1],e[2],e[3],f[0],f[1],f[2],f[3],g[0],g[1],g[2],g[3],h[0],h[1],h[2],h[3]]}
#[repr(u8)]
pub enum PoolV1TransitionKind {
    PrivateTransfer = 1,
    Withdrawal = 2,
}
pub struct Marker{pub transition_kind:PoolV1TransitionKind,pub pool:[u8;32],pub deployment_domain:[u8;32],pub nullifier:[u32;8],pub retained_anchor_sequence:u64,pub retained_anchor_root:[u32;8],pub verifier_profile:[u8;32],pub verifier_release:[u8;32]}
pub fn encode_marker(marker:Marker)->[u8;32]{encode(marker.nullifier)}
