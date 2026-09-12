//! Exact narrow port of authenticated_c1.rs through authenticate; the decoder
//! and its 1024^3 public-matrix precomputation are deliberately not rebuilt.
//! ExtractionCheck.py checks this slice byte-for-byte against the source.
use super::*;
pub const OPEN_FIBRES:usize=256;
#[derive(Clone)]
pub struct C1Openings {pub ids:Vec<u32>,pub leaves:Vec<Vec<u8>>,pub salts:Vec<[u8;32]>,pub frontier:Vec<u8>}
pub fn read31(b:&[u8],bit:usize)->Result<M31,Error>{
    let mut v=0;for j in 0..31{v|=(((b[(bit+j)/8]>>((bit+j)%8))&1)as u32)<<j;}
    if v>=corelib::field::P {Err(Error::Canonical)}else{Ok(M31(v))}
}
pub fn put31(b:&mut[u8],bit:usize,x:M31){assert!(x.0<corelib::field::P);
    for j in 0..31 {b[(bit+j)/8]|=(((x.0>>j)&1)as u8)<<((bit+j)%8);}
}
pub fn authenticate(root:[u8;26],o:&C1Openings)->Result<Vec<Vec<M31>>,Error>{
    if o.ids!=(0..256).collect::<Vec<u32>>()||o.leaves.len()!=256||o.salts.len()!=256{return Err(Error::Shape)}
    let mut entries=Vec::new();let mut values=vec![vec![M31::ZERO;1024];16];
    for i in 0..256{
        if o.leaves[i].len()!=403{return Err(Error::Length)}
        for slot in 0..4{for col in 0..26{
            let v=read31(&o.leaves[i],31*(slot*26+col))?;
            if col<16{values[col][4*i+slot]=v;}
        }}
        let leaf=private_leaf_hash_v7(hash,V7_C1_TREE_TAG,&o.leaves[i],&o.salts[i]);
        entries.push((o.ids[i],leaf,leaf));
    }
    // Reuse the exact selected checker twice on the SAME C1 tree. This is
    // not a C2 authentication claim. Frontier bytes are supplied once and
    // borrowed twice; duplicated hash work is extractor work.
    if !verify_two_minimal_subtrees_v7_bytes(hash,(&root,&root),18,&entries,
        (&o.frontier,&o.frontier),&mut vec![],&mut vec![]){return Err(Error::Authentication)}
    Ok(values)
}
