extern crate aspis_core as corelib;
use corelib::v7_merkle208::{private_leaf_hash_v7,truncate_sha256_v7,V7_C2_TREE_TAG};
use sha2::{Digest,Sha256};
#[path="leaf_record.rs"] mod leaf_record;
fn hash(parts:&[&[u8]])->[u8;32]{let mut h=Sha256::new();for p in parts{h.update(p);}h.finalize().into()}
std::thread_local!{static EXPECTED:std::cell::RefCell<Vec<u8>>=const{std::cell::RefCell::new(Vec::new())};}
fn capture(parts:&[&[u8]])->[u8;32]{
    assert_eq!(parts.iter().map(|s|s.len()).collect::<Vec<_>>(),[2,218]);
    let flat:Vec<u8>=parts.iter().flat_map(|s|s.iter().copied()).collect();
    EXPECTED.with(|e|assert_eq!(*e.borrow(),flat));hash(parts)
}
fn check(r:&[u8;621]){
    let salt:&[u8;32]=r[589..621].try_into().unwrap();
    let mut expected=vec![0x10,V7_C2_TREE_TAG];expected.extend(&r[403..589]);expected.extend(salt);
    EXPECTED.with(|e|*e.borrow_mut()=expected);
    assert_eq!(leaf_record::c2(capture,r),private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&r[403..589],salt));
}
fn main(){
    for position in 0..621{for value in 0..=255u8{let mut r=[0;621];r[position]=value;check(&r);}}
    let mut rng=0x6c65_6166_7638_2026u64;
    for _ in 0..1024{let r=core::array::from_fn(|_|{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;rng as u8});check(&r);}
    println!("R86_LEAF literal_bytes_and_sha=160000 identical_record_layout=true parser_gate=full_wire_controls");
}
