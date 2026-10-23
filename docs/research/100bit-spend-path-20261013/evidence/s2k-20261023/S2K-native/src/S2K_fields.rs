// Individual source field writes; arbitrary complete original buffer.
#[kani::proof]
#[kani::unwind(34)]
fn S2K_field_magic() {
    let mut output:[u8;688]=kani::any();
    let afterstate=PoolV1PairVerifiedAfterstateV1 { next_pair_index:kani::any(), next_root:digest(), next_frontier:[[M31(0);8];20] };
    let j:usize=kani::any(); kani::assume(j<4);
    let i:usize=kani::any(); kani::assume(i<688 && (i<0 || i>=4));
    let before=output[i];
    output[..4].copy_from_slice(&POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC);
    assert_eq!(output[0+j],POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC[j]);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==3);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_field_transport() {
    let mut output:[u8;688]=kani::any();
    let afterstate=PoolV1PairVerifiedAfterstateV1 { next_pair_index:kani::any(), next_root:digest(), next_frontier:[[M31(0);8];20] };
    let j:usize=kani::any(); kani::assume(j<1);
    let i:usize=kani::any(); kani::assume(i<688 && (i<4 || i>=5));
    let before=output[i];
    output[4] = POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;
    assert_eq!(output[4+j],POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==0);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_field_storage() {
    let mut output:[u8;688]=kani::any();
    let afterstate=PoolV1PairVerifiedAfterstateV1 { next_pair_index:kani::any(), next_root:digest(), next_frontier:[[M31(0);8];20] };
    let j:usize=kani::any(); kani::assume(j<1);
    let i:usize=kani::any(); kani::assume(i<688 && (i<5 || i>=6));
    let before=output[i];
    output[5] = POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION;
    assert_eq!(output[5+j],POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==0);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_field_digest_version() {
    let mut output:[u8;688]=kani::any();
    let afterstate=PoolV1PairVerifiedAfterstateV1 { next_pair_index:kani::any(), next_root:digest(), next_frontier:[[M31(0);8];20] };
    let j:usize=kani::any(); kani::assume(j<1);
    let i:usize=kani::any(); kani::assume(i<688 && (i<6 || i>=7));
    let before=output[i];
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    assert_eq!(output[6+j],POOL_V1_DIGEST_ENCODING_VERSION);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==0);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_field_success() {
    let mut output:[u8;688]=kani::any();
    let afterstate=PoolV1PairVerifiedAfterstateV1 { next_pair_index:kani::any(), next_root:digest(), next_frontier:[[M31(0);8];20] };
    let j:usize=kani::any(); kani::assume(j<1);
    let i:usize=kani::any(); kani::assume(i<688 && (i<7 || i>=8));
    let before=output[i];
    output[7] = 1;
    assert_eq!(output[7+j],1);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==0);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_field_index() {
    let mut output:[u8;688]=kani::any();
    let afterstate=PoolV1PairVerifiedAfterstateV1 { next_pair_index:kani::any(), next_root:digest(), next_frontier:[[M31(0);8];20] };
    let j:usize=kani::any(); kani::assume(j<8);
    let i:usize=kani::any(); kani::assume(i<688 && (i<8 || i>=16));
    let before=output[i];
    output[8..16].copy_from_slice(&afterstate.next_pair_index.to_le_bytes());
    assert_eq!(output[8+j],afterstate.next_pair_index.to_le_bytes()[j]);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==7);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_field_root() {
    let mut output:[u8;688]=kani::any();
    let afterstate=PoolV1PairVerifiedAfterstateV1 { next_pair_index:kani::any(), next_root:digest(), next_frontier:[[M31(0);8];20] };
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688 && (i<16 || i>=48));
    let before=output[i];
    let source=encode_digest_canonical(&afterstate.next_root);
    S2K_copy32(&mut output[16..48],&source,j,source[j]);
    assert_eq!(output[16+j],(afterstate.next_root[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==31);
}
