#[derive(Clone, Copy)]
struct CommonPublicV1 {
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor_sequence: u64,
    anchor_root: Digest,
    nullifier: Digest,
    asset_id: M31,
}