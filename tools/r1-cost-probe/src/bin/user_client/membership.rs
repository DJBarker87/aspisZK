//! Local membership from complete, non-selectively obtained public lane leaves.
use crate::diagnostics::{anyhow,ensure,err,Result};
use aspis_core::field::{M31,P};
use aspis_statement::{poseidon2::Digest,pool_v1::*,pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1};
use serde_json::Value;
use aspis_pool::POOL_V1_PAIR_EMPTY_ROOTS;
fn digest(v:&Value)->Result<Digest>{
 let text=crate::value_text(v)?;let s=text.as_str();
 ensure!(s.len()==64&&s.is_ascii(),"public commitment width");
 let out=[M31(0);8];
 let mut result=Ok(out);for i in 0..8{result=insert_limb(result,s,i);}result
}
fn insert_limb(out:Result<Digest>,s:&str,i:usize)->Result<Digest>{let mut out=out?;out[i]=limb(s,i)?;Ok(out)}
fn limb(s:&str,i:usize)->Result<M31>{
 let mut result=Ok([0u8;4]);for j in 0..4{result=insert_byte(result,s,i,j);}let b=result?;
 let x=u32::from_le_bytes(b);ensure!(x<P,"noncanonical public field");Ok(M31(x))
}
fn insert_byte(out:Result<[u8;4]>,s:&str,i:usize,j:usize)->Result<[u8;4]>{let mut out=out?;out[j]=u8::from_str_radix(&s[8*i+2*j..8*i+2*j+2],16).map_err(err)?;Ok(out)}
fn leaf(v:&Value)->Result<PoolV1PairLeafWitnessV1>{
 let a=crate::public_array(v)?;
 ensure!(a.len()==2,"public pair width");let first=digest(&a[0])?;let second=digest(&a[1])?;
 if second==[M31(0);8]{PoolV1PairLeafWitnessV1::single_output(first).map_err(err)}else{PoolV1PairLeafWitnessV1::two_outputs(first,second).map_err(err)}
}
fn lane(v:&Value)->Result<Vec<PoolV1PairLeafWitnessV1>>{
 let a=crate::public_array(v)?;
 ensure!(a.len()<=1<<20u32,"lane exceeds tree capacity");
 let mut out=Ok(Vec::with_capacity(a.len()));let mut i=0;while i<a.len(){out=push_leaf(out,&a[i]);i+=1;}out
}
fn push_leaf(out:Result<Vec<PoolV1PairLeafWitnessV1>>,v:&Value)->Result<Vec<PoolV1PairLeafWitnessV1>>{let mut out=out?;out.push(leaf(v)?);Ok(out)}
fn hashes(leaves:&[PoolV1PairLeafWitnessV1])->Result<Vec<Digest>>{
 let mut out=Ok(Vec::with_capacity(leaves.len()));let mut i=0;while i<leaves.len(){out=push_hash(out,&leaves[i]);i+=1;}out
}
fn push_hash(out:Result<Vec<Digest>>,v:&PoolV1PairLeafWitnessV1)->Result<Vec<Digest>>{let mut out=out?;out.push(v.leaf_digest().map_err(err)?);Ok(out)}
fn parent_level(nodes:&[Digest],empty:Digest)->Vec<Digest>{
 let mut out=Vec::with_capacity(nodes.len().div_ceil(2).max(1));
 if nodes.is_empty(){out.push(pool_v1_tree_parent(&empty,&empty));}else{
 let mut i=0;while i<nodes.len(){let right=if i+1<nodes.len(){nodes[i+1]}else{empty};out.push(pool_v1_tree_parent(&nodes[i],&right));i+=2;}}
 out
}
fn path(mut nodes:Vec<Digest>,mut index:usize)->(Digest,[Digest;20]){
 let mut siblings=[POOL_V1_PAIR_EMPTY_ROOTS[0];20];
 for level in 0..20{siblings[level]=if (index^1)<nodes.len(){nodes[index^1]}else{POOL_V1_PAIR_EMPTY_ROOTS[level]};index>>=1u32;nodes=parent_level(&nodes,POOL_V1_PAIR_EMPTY_ROOTS[level]);}
 (nodes[0],siblings)
}
fn locate(leaves:&[PoolV1PairLeafWitnessV1],cm:Digest)->(Option<(usize,bool)>,usize){
 let mut found=None;let mut count=0;
 let mut i=0;while i<leaves.len(){let p=leaves[i];if p.first_commitment==cm{found=Some((i,false));count+=1;}if p.second_occupied==M31(1)&&p.second_commitment==cm{found=Some((i,true));count+=1;}i+=1;}
 (found,count)
}
struct Lane {root:Digest,selected:Option<(PoolV1PairLeafWitnessV1,usize,bool,[Digest;20])>}
fn prepare(v:&Value,cm:Digest)->Result<Lane>{
 let leaves=lane(v)?;let (selected,count)=locate(&leaves,cm);ensure!(count<=1,"duplicate input commitment");let index=match selected{Some((i,_))=>i,None=>0};
 let (root,siblings)=path(hashes(&leaves)?,index);
 Ok(Lane{root,selected:match selected{Some((i,second))=>Some((leaves[i],i,second,siblings)),None=>None}})
}
fn push_lane(out:Result<Vec<Lane>>,v:&Value,cm:Digest)->Result<Vec<Lane>>{let mut out=out?;out.push(prepare(v,cm)?);Ok(out)}
fn prepare_all(q:&Value,cm:Digest)->Result<Vec<Lane>>{
 let public_leaves=crate::public_field(q,"lane_leaf_sets");
 let all=crate::public_array(&public_leaves)?;
 ensure!(all.len()==8,"all eight public lane leaf sets required");
 let mut prepared=Ok(Vec::with_capacity(8));let mut l=0;
 while l<all.len(){prepared=push_lane(prepared,&all[l],cm);l+=1;}prepared
}
fn collect_roots(prepared:&[Lane])->Vec<Digest>{
 let mut roots=Vec::with_capacity(8);let mut l=0;
 while l<prepared.len(){roots.push(prepared[l].root);l+=1;}roots
}
struct Selection {lane:usize,pair:PoolV1PairLeafWitnessV1,index:usize,second:bool,siblings:[Digest;20]}
fn lane_selection(lane:usize,p:&Lane)->Option<Selection>{
 match p.selected{Some((pair,index,second,siblings))=>Some(Selection{lane,pair,index,second,siblings}),None=>None}
}
fn collect_selection(prepared:&[Lane])->Result<Selection>{
 let mut selected=None;let mut matches=0;let mut l=0;
 while l<prepared.len(){
  match lane_selection(l,&prepared[l]){Some(s)=>{matches+=1;selected=Some(s);},None=>{}}
  l+=1;
 }
 ensure!(matches==1,"input commitment must occur in one lane");
 selected.ok_or_else(||anyhow!("input absent"))
}
fn super_path(mut roots:Vec<Digest>,lane:usize,anchor:Digest)->Result<([Digest;3],[bool;3])>{
 let mut supers=[roots[0];3];let mut directions=[false;3];let mut index=lane;
 for level in 0..3{supers[level]=roots[index^1];directions[level]=index%2==1;index>>=1u32;roots=parent_level(&roots,POOL_V1_PAIR_EMPTY_ROOTS[0]);}
 ensure!(roots[0]==anchor,"complete public leaves do not reconstruct checkpoint");
 Ok((supers,directions))
}
fn witness(s:Selection,roots:Vec<Digest>,k:Digest,salt:Digest,value:u32,anchor:Digest)->Result<PoolV1PairForestInputNoteWitnessV1>{
 let (supers,directions)=super_path(roots,s.lane,anchor)?;
 Ok(PoolV1PairForestInputNoteWitnessV1{pair:PoolV1PairInputNoteWitnessV1{nullifier_key:k,salt,value,pair_leaf:s.pair,selected_second:s.second,membership:PoolV1MembershipWitnessV1{siblings:s.siblings,index:s.index as u32}},super_root_siblings:supers,super_root_directions:directions})
}
pub fn input(q:&Value,cm:Digest,k:Digest,salt:Digest,value:u32,anchor:Digest)->Result<PoolV1PairForestInputNoteWitnessV1>{
 let prepared=prepare_all(q,cm)?;
 let roots=collect_roots(&prepared);
 let selected=collect_selection(&prepared)?;
 witness(selected,roots,k,salt,value,anchor)
}
