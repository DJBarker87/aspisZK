//! R13 draft source-integration checks. Research-only; NOT compiled in Chat.
//! Install as a #[cfg(test)] child of state_only_hiding.rs so the real private
//! builder, mask columns and expander are used. No production path changes.
use super::*;
use std::cell::RefCell;
use std::collections::BTreeMap;
use sha2::{Digest, Sha256};
use aspis_core::v7_merkle208::{private_leaf_hash_v7, node_hash_v7, V7_C2_TREE_TAG};
use crate::circle_candidate::CircleEncoder;
use crate::state_only_spend_candidate::encode_state_only_spend_c2_columns;
#[path = "r13_expected.rs"] mod expected;

thread_local! {
    static OVERRIDES: RefCell<BTreeMap<Vec<u8>,[u8;32]>> = RefCell::new(BTreeMap::new());
}
fn base_hash(parts: &[&[u8]]) -> [u8;32] {
    let mut h=Sha256::new(); for p in parts {h.update(p);} h.finalize().into()
}
fn test_oracle(parts: &[&[u8]]) -> [u8;32] {
    let key=parts.concat();
    OVERRIDES.with(|cell| cell.borrow().get(&key).copied())
        .unwrap_or_else(||base_hash(parts))
}
struct Reset;
impl Drop for Reset {fn drop(&mut self){OVERRIDES.with(|c|c.borrow_mut().clear());}}
fn read_u32(b:&[u8],cursor:&mut usize)->usize {
    let end=cursor.checked_add(4).expect("length overflow");
    let x=u32::from_le_bytes(b.get(*cursor..end).expect("truncated fixture").try_into().unwrap());
    *cursor=end;x as usize
}
fn fixture()->BTreeMap<Vec<u8>,[u8;32]> {
    let b=include_bytes!("r13_expansion_overrides.bin");
    assert_eq!(&b[..8],b"R13EXP01");let mut cursor=8;
    let n=read_u32(b,&mut cursor);let mut out=BTreeMap::new();
    for _ in 0..n {
        let len=read_u32(b,&mut cursor);let end=cursor.checked_add(len).unwrap();
        let key=b.get(cursor..end).expect("fixture key").to_vec();cursor=end;
        let end=cursor.checked_add(32).unwrap();
        let val=b.get(cursor..end).expect("fixture answer").try_into().unwrap();cursor=end;
        assert!(out.insert(key,val).is_none(),"duplicate fixture input");
    }
    assert_eq!(cursor,b.len());assert_eq!(n,282);out
}
fn material(hash: aspis_core::HashFn)->StateOnlyMaskMaterial {
    let context=StateOnlyHidingContext::pool_v1_pair_forest_v1([0x45;32],[0x23;32]);
    let cells=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let active=pool_v1_pair_forest_copy_active_rows().unwrap();
    let mut nonces=InMemoryStateOnlyMaskNonceStore::default();
    build_mask_material_for_layout(hash,[0xab;32],context,&[0x67;32],&mut nonces,&cells,&active).unwrap()
}
fn digest(values:&[QM31])->[u8;32] {
    let mut h=Sha256::new();for q in values {
        for v in [q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0] {h.update(v.to_le_bytes());}
    } h.finalize().into()
}
fn packed_fiber(cols:&[Vec<QM31>],fiber:usize)->Vec<u8> {
    // Exact helper-major/slot-major/tower-limb order in packed_c2_fiber.
    let mut out=Vec::with_capacity(186);let mut buffer=0u64;let mut filled=0u32;
    for col in cols {for slot in 0..4 {
        let q=col[4*fiber+slot];for v in [q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0] {
            assert!(v<aspis_core::field::P);buffer|=u64::from(v)<<filled;filled+=31;
            while filled>=8 {out.push(buffer as u8);buffer>>=8;filled-=8;}
        }
    }}
    assert_eq!(filled,0);assert_eq!(out.len(),186);out
}
fn leaf_key(p:&[u8],salt:&[u8;32])->Vec<u8> {
    [&[0x10,V7_C2_TREE_TAG][..],p,&salt[..]].concat()
}

#[test]
fn r13_real_main_codec_preserves_every_non_g_component() {
    let _reset=Reset;
    OVERRIDES.with(|c|c.borrow_mut().clear());let before=material(test_oracle);
    OVERRIDES.with(|c|*c.borrow_mut()=fixture());let after=material(test_oracle);
    assert_eq!(before.c1,after.c1);assert_eq!(before.mask_only_c1,after.mask_only_c1);
    assert_eq!(before.h1_padding,after.h1_padding);assert_eq!(before.mask_nonce,after.mask_nonce);
    assert_eq!(digest(&before.g),expected::BEFORE_G);assert_eq!(digest(&after.g),expected::AFTER_G);
    assert_eq!(digest(&before.h1_padding),expected::H1);assert_ne!(before.g,after.g);
}

#[test]
fn r13_real_circle_payloads_and_typed_leaves_swap_full_answers() {
    // This binds the real encoder and leaf API at eight selected fibres. It is
    // NOT a full q22 prover run or a test of R12 offsets under actual FS roots.
    let _reset=Reset;
    OVERRIDES.with(|c|c.borrow_mut().clear());let before=material(test_oracle);
    OVERRIDES.with(|c|*c.borrow_mut()=fixture());let after=material(test_oracle);
    let encoder=CircleEncoder::new_for_domain_log(20);
    let first=encode_state_only_spend_c2_columns(&encoder,
        &[before.h1_padding.clone(),before.g.clone(),vec![QM31::ZERO;1024]]).unwrap();
    let second=encode_state_only_spend_c2_columns(&encoder,
        &[after.h1_padding.clone(),after.g.clone(),vec![QM31::ZERO;1024]]).unwrap();
    assert_eq!(first[0],second[0]);assert_eq!(first[2],second[2]);
    let mut old_roots=Vec::new();let mut new_payloads=Vec::new();let mut keys=Vec::new();
    for i in 0..8usize {
        let salt=base_hash(&[b"r13-real-encoder-salt",&(i as u32).to_le_bytes()]);
        let old=packed_fiber(&first,i);let new=packed_fiber(&second,i);
        let a=leaf_key(&old,&salt);let b=leaf_key(&new,&salt);
        let ha=test_oracle(&[&a]);let hb=test_oracle(&[&b]);
        old_roots.push(ha[..26].try_into().unwrap());
        new_payloads.push((new,salt,ha));keys.push((a,b,ha,hb));
    }
    // Reject cross-leaf address aliases before applying the simultaneous swaps.
    let mut owner=BTreeMap::new();for(i,(a,b,_,_))in keys.iter().enumerate(){
        for key in [a,b] {if let Some(old)=owner.insert(key.clone(),i){assert_eq!(old,i);}}
    }
    OVERRIDES.with(|cell|{let mut m=cell.borrow_mut();for(a,b,ha,hb)in &keys{m.insert(a.clone(),*hb);m.insert(b.clone(),*ha);}});
    let mut new_roots=Vec::new();
    for(p,salt,ha)in new_payloads {
        assert_eq!(test_oracle(&[&leaf_key(&p,&salt)]),ha);
        new_roots.push(private_leaf_hash_v7(test_oracle,V7_C2_TREE_TAG,&p,&salt));
    }
    assert_eq!(old_roots,new_roots);
    let root=|mut layer:Vec<[u8;26]>| {while layer.len()>1{
        layer=layer.chunks_exact(2).map(|p|node_hash_v7(test_oracle,&p[0],&p[1])).collect();}layer[0]};
    assert_eq!(root(old_roots),root(new_roots));
}
