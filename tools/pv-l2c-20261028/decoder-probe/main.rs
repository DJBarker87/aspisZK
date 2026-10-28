use aspis_core::field::{M31, P};
use aspis_statement::{decode_digest_canonical, derive_owner_key, encode_digest_canonical,
    poseidon2::Digest, pool_v1::{pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent}};
#[path="domain_constants.rs"] mod spend;
#[path="hash_reference.rs"] mod reference;
#[path="frozen_empty_roots.rs"] mod frozen_empty_roots;
use frozen_empty_roots::POOL_V1_PAIR_EMPTY_ROOTS;

// Exact body of devnet_spend/plan.rs::digest, checked by decoder-source-check.py.
fn digest(seed:u32)->Digest{core::array::from_fn(|i|M31((seed+17*i as u32+1)%P))}
fn canonical(d: &Digest) { assert!(d.iter().all(|v| v.0 < P)); }
fn main() {
    assert!(!cfg!(debug_assertions));
    if std::env::args().nth(1).as_deref()==Some("account-only") {account_codec_cases();return}
    let cases = [0, 1, P - 1, P, P + 1, u32::MAX];
    for x in cases {
        let got = M31::from_le_bytes(x.to_le_bytes());
        assert_eq!(got, if x < P { Some(M31(x)) } else { None });
        for lane in 0..8 {
            let mut bytes = [0u8; 32];
            bytes[lane*4..lane*4+4].copy_from_slice(&x.to_le_bytes());
            match decode_digest_canonical(&bytes) {
                Ok(d) => { assert!(x < P); canonical(&d); assert_eq!(d[lane].0,x); }
                Err(_) => assert!(x >= P),
            }
        }
    }
    for seed in (0..126).chain([u32::MAX - 1, u32::MAX]) {
        let k = digest(seed); canonical(&k);
        let salt = digest(seed.wrapping_add(100)); canonical(&salt);
        let owner = derive_owner_key(&k); canonical(&owner);
        assert_eq!(owner,reference::hash_owner_key(&k));
        let cm = pool_v1_note_commitment(&owner,1000,M31(77),&salt); canonical(&cm);
        let mut note = owner.to_vec(); note.extend([M31(1000),M31(77)]); note.extend(salt);
        assert_eq!(cm,reference::hash_note_commitment(&note));
        let nf = pool_v1_nullifier(&k,&salt); canonical(&nf);
        let mut nf_input=k.to_vec();nf_input.extend(salt);
        assert_eq!(nf,reference::hash_nullifier(&nf_input));
        let parent=pool_v1_tree_parent(&cm,&nf);canonical(&parent);
        assert_eq!(parent,reference::merkle_node_compress_v3(&cm,&nf));
        assert_eq!(decode_digest_canonical(&encode_digest_canonical(&k)).unwrap(), k);
    }
    println!("scalar_boundary_cases=6 digest_boundary_cases=48 generated_seed_cases=128");
    println!("actual_native_codec_and_hashes=true exact_body_generator_copy=true finite_validation_only=true");
    println!("same_input_native_owned_external_hash_comparisons=512");
}

// Ordered digest field cut in decode_tree_image_unvalidated, after its fixed
// length/header guards. All native decoder calls and writes retain order.
fn tree_fields(bytes: &[u8]) -> Result<(Digest,[Digest;20]),aspis_statement::pool_v1::PoolV1TreeError> {
    use aspis_statement::pool_v1::PoolV1TreeError;
    let root=decode_digest_canonical(bytes[16..48].try_into().unwrap()).map_err(|_|PoolV1TreeError::NonCanonicalDigest)?;
    let mut frontier=[[M31::ZERO;8];20];
    for (level,node) in frontier.iter_mut().enumerate() {
        let start=48+level*32;
        *node=decode_digest_canonical(bytes[start..start+32].try_into().unwrap()).map_err(|_|PoolV1TreeError::NonCanonicalDigest)?;
    }
    Ok((root,frontier))
}
fn account_codec_cases() {
    use aspis_statement::pool_v1::*;
    let empty=&POOL_V1_PAIR_EMPTY_ROOTS;
    let mut tree=IncrementalMerkleTreeV1::from_parts_with_empty_roots(0,empty[20],core::array::from_fn(|l|empty[l]),empty).unwrap();
    let mut rejected=0;
    for index in 0..4 {
        let lane=PoolV1PairForestLaneStateV1{bump:0,master:[1;32],lane_id:0,tree};
        let bytes=encode_pool_v1_pair_forest_lane_state_v1(&lane,empty).unwrap();
        let native=decode_pool_v1_pair_forest_lane_state_v1(&bytes,empty).unwrap();
        let fields=tree_fields(&bytes[80..]).unwrap();
        assert_eq!((native.tree.root,native.tree.frontier),fields);
        canonical(&fields.0);for d in &fields.1{canonical(d)}
        for field in 0..21 {for limb in 0..8 {
            let mut bad=bytes;
            let off=80+16+32*field+4*limb;
            bad[off..off+4].copy_from_slice(&P.to_le_bytes());
            assert!(decode_pool_v1_pair_forest_lane_state_v1(&bad,empty).is_err());
            assert!(tree_fields(&bad[80..]).is_err());
            rejected+=1;
        }}
        let cp=PoolV1PairForestCheckpointV1{bump:0,master:[1;32],deployment_domain:[5;32],checkpoint_sequence:42,global_root:tree.root,lane_sequences:[index;8]};
        let cb=encode_pool_v1_pair_forest_checkpoint_v1(&cp).unwrap();
        assert_eq!(decode_pool_v1_pair_forest_checkpoint_v1(&cb).unwrap(),cp);
        for limb in 0..8 {
            let mut bad=cb;let off=80+4*limb;
            bad[off..off+4].copy_from_slice(&P.to_le_bytes());
            assert!(decode_pool_v1_pair_forest_checkpoint_v1(&bad).is_err());
            rejected+=1;
        }
        tree=tree.append_one_with_empty_roots(digest(900+index as u32),empty).unwrap().0;
    }
    assert_eq!(rejected,704);
    println!("lane_ordered_field_comparisons=4 checkpoint_roundtrips=4 noncanonical_account_rejections=704");
}
