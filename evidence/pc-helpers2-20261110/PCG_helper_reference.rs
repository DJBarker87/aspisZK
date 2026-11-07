#[derive(Clone,Copy)]
pub struct Tree{pub next_leaf_index:u64,pub root:[u32;8],pub frontier:[[u32;8];32]}
pub fn owned_tree(inner:Tree)->Tree{inner}
pub fn full(filled:u16)->bool{usize::from(filled)==256}
pub fn get_index(page:u64,filled:u16,sequence:u64)->Option<usize>{let p=sequence/256;let slot=(sequence%256) as u16;if p!=page||slot>=filled{None}else{Some(usize::from(slot))}}
pub fn canonical_step(prefix:bool,limb:u32)->bool{prefix && limb<2147483647}
