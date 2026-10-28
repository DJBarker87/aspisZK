use aspis_core::field::{M31, P};
use aspis_statement::{decode_digest_canonical, derive_owner_key, encode_digest_canonical,
    poseidon2::Digest, pool_v1::{pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent}};
#[path="domain_constants.rs"] mod spend;
#[path="hash_reference.rs"] mod reference;

// Exact body of devnet_spend/plan.rs::digest, checked by decoder-source-check.py.
fn digest(seed:u32)->Digest{core::array::from_fn(|i|M31((seed+17*i as u32+1)%P))}
fn canonical(d: &Digest) { assert!(d.iter().all(|v| v.0 < P)); }
fn main() {
    assert!(!cfg!(debug_assertions));
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
