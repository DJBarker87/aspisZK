use super::*;
use crate::PCG_Address::KMX_copy_nonoverlapping;
fn canonical(d:&Digest)->bool{d.iter().all(|v|v.0<aspis_core::field::P)}
fn diagnostic_parent(l:&Digest,r:&Digest)->Digest{
 assert!(canonical(l)&&canonical(r));
 [aspis_core::field::M31((l[0].0.rotate_left(1)^r[0].0.rotate_right(1))&0x3fffffff),aspis_core::field::M31((l[1].0.rotate_left(1)^r[1].0.rotate_right(1))&0x3fffffff),aspis_core::field::M31((l[2].0.rotate_left(1)^r[2].0.rotate_right(1))&0x3fffffff),aspis_core::field::M31((l[3].0.rotate_left(1)^r[3].0.rotate_right(1))&0x3fffffff),aspis_core::field::M31((l[4].0.rotate_left(1)^r[4].0.rotate_right(1))&0x3fffffff),aspis_core::field::M31((l[5].0.rotate_left(1)^r[5].0.rotate_right(1))&0x3fffffff),aspis_core::field::M31((l[6].0.rotate_left(1)^r[6].0.rotate_right(1))&0x3fffffff),aspis_core::field::M31((l[7].0.rotate_left(1)^r[7].0.rotate_right(1))&0x3fffffff)]
}
struct Log{replies:[Digest;7],left:[Digest;7],right:[Digest;7],calls:usize}
fn parent_window(left:&Digest,right:&Digest,log:&mut Log)->Digest{
 assert!(canonical(left)&&canonical(right));let k=log.calls;log.left[k]=*left;log.right[k]=*right;log.calls+=1;log.replies[k]
}
// Exact frozen324 body, with only child calls given their local oracle log.
fn global_window(lane_roots:&[Digest;8],log:&mut Log)->Digest{
 let level_one=[parent_window(&lane_roots[0],&lane_roots[1],log),parent_window(&lane_roots[2],&lane_roots[3],log),parent_window(&lane_roots[4],&lane_roots[5],log),parent_window(&lane_roots[6],&lane_roots[7],log)];
 let level_two=[parent_window(&level_one[0],&level_one[1],log),parent_window(&level_one[2],&level_one[3],log)];
 parent_window(&level_two[0],&level_two[1],log)
}
#[kani::proof] #[kani::unwind(512)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn seven_calls(){
 let roots:[Digest;8]=kani::any();let replies:[Digest;7]=kani::any();for d in roots.iter(){kani::assume(canonical(d));}for d in replies.iter(){kani::assume(canonical(d));}
 let mut log=Log{replies,left:[[aspis_core::field::M31(0);8];7],right:[[aspis_core::field::M31(0);8];7],calls:0};let out=global_window(&roots,&mut log);let i:usize=kani::any();let limb:usize=kani::any();kani::assume(i<7&&limb<8);
 let left=match i{0=>roots[0],1=>roots[2],2=>roots[4],3=>roots[6],4=>replies[0],5=>replies[2],6=>replies[4],_=>unreachable!()};let right=match i{0=>roots[1],1=>roots[3],2=>roots[5],3=>roots[7],4=>replies[1],5=>replies[3],6=>replies[5],_=>unreachable!()};
 assert_eq!(log.calls,7);assert_eq!(log.left[i][limb].0,left[limb].0);assert_eq!(log.right[i][limb].0,right[limb].0);assert!((out[limb].0==replies[6][limb].0)!=cfg!(PCG_NEG_GLOBAL));
}
#[kani::proof] #[kani::unwind(512)]
#[kani::stub(aspis_statement::pool_v1::pool_v1_tree_parent,diagnostic_parent)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn actual_call_structure(){
 let roots:[Digest;8]=kani::any();for d in roots.iter(){kani::assume(canonical(d));}
 let got=pool_v1_pair_forest_global_root_v1(&roots);
 let a=diagnostic_parent(&roots[0],&roots[1]);let b=diagnostic_parent(&roots[2],&roots[3]);let c=diagnostic_parent(&roots[4],&roots[5]);let d=diagnostic_parent(&roots[6],&roots[7]);let e=diagnostic_parent(&a,&b);let f=diagnostic_parent(&c,&d);let expected=diagnostic_parent(&e,&f);
 let i:usize=kani::any();kani::assume(i<8);assert!((got[i].0==expected[i].0)!=cfg!(PCG_NEG_GLOBAL));
}
