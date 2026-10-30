//! Local membership from complete, non-selectively obtained public lane leaves.
use crate::diagnostics::{anyhow,ensure,err,Result};
use aspis_core::field::{M31,P};
use aspis_statement::{poseidon2::Digest,pool_v1::*,pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1};
use serde_json::Value;
use aspis_pool::POOL_V1_PAIR_EMPTY_ROOTS;
fn digest(v:&Value)->Result<Digest>{
 let s=v.as_str().ok_or_else(||anyhow!("public commitment must be hex"))?;
 ensure!(s.len()==64&&s.is_ascii(),"public commitment width");
 let mut out=[M31(0);8];
 let mut result=Ok(out);for i in 0..8{result=insert_limb(result,s,i);}result
}
fn insert_limb(out:Result<Digest>,s:&str,i:usize)->Result<Digest>{let mut out=out?;out[i]=limb(s,i)?;Ok(out)}
fn limb(s:&str,i:usize)->Result<M31>{
 let mut result=Ok([0u8;4]);for j in 0..4{result=insert_byte(result,s,i,j);}let b=result?;
 let x=u32::from_le_bytes(b);ensure!(x<P,"noncanonical public field");Ok(M31(x))
}
fn insert_byte(out:Result<[u8;4]>,s:&str,i:usize,j:usize)->Result<[u8;4]>{let mut out=out?;out[j]=u8::from_str_radix(&s[8*i+2*j..8*i+2*j+2],16).map_err(err)?;Ok(out)}
fn leaf(v:&Value)->Result<PoolV1PairLeafWitnessV1>{
 let a=v.as_array().ok_or_else(||anyhow!("public pair must be array"))?;
 ensure!(a.len()==2,"public pair width");let first=digest(&a[0])?;let second=digest(&a[1])?;
 if second==[M31(0);8]{PoolV1PairLeafWitnessV1::single_output(first).map_err(err)}else{PoolV1PairLeafWitnessV1::two_outputs(first,second).map_err(err)}
}
fn lane(v:&Value)->Result<Vec<PoolV1PairLeafWitnessV1>>{
 let a=v.as_array().ok_or_else(||anyhow!("lane must contain complete public pairs"))?;
 ensure!(a.len()<=1<<20,"lane exceeds tree capacity");
 let mut out=Ok(Vec::with_capacity(a.len()));for v in a{out=push_leaf(out,v);}out
}
fn push_leaf(out:Result<Vec<PoolV1PairLeafWitnessV1>>,v:&Value)->Result<Vec<PoolV1PairLeafWitnessV1>>{let mut out=out?;out.push(leaf(v)?);Ok(out)}
fn hashes(leaves:&[PoolV1PairLeafWitnessV1])->Result<Vec<Digest>>{
 let mut out=Ok(Vec::with_capacity(leaves.len()));for v in leaves{out=push_hash(out,v);}out
}
fn push_hash(out:Result<Vec<Digest>>,v:&PoolV1PairLeafWitnessV1)->Result<Vec<Digest>>{let mut out=out?;out.push(v.leaf_digest().map_err(err)?);Ok(out)}
fn parent_level(nodes:&[Digest],empty:Digest)->Vec<Digest>{
 let mut out=Vec::with_capacity(nodes.len().div_ceil(2).max(1));
 if nodes.is_empty(){out.push(pool_v1_tree_parent(&empty,&empty));}else{
 let mut i=0;while i<nodes.len(){let right=nodes.get(i+1).copied().unwrap_or(empty);out.push(pool_v1_tree_parent(&nodes[i],&right));i+=2;}}
 out
}
fn path(mut nodes:Vec<Digest>,mut index:usize)->(Digest,[Digest;20]){
 let mut siblings=[POOL_V1_PAIR_EMPTY_ROOTS[0];20];
 for level in 0..20{siblings[level]=nodes.get(index^1).copied().unwrap_or(POOL_V1_PAIR_EMPTY_ROOTS[level]);index>>=1;nodes=parent_level(&nodes,POOL_V1_PAIR_EMPTY_ROOTS[level]);}
 (nodes[0],siblings)
}
fn locate(leaves:&[PoolV1PairLeafWitnessV1],cm:Digest)->(Option<(usize,bool)>,usize){
 let mut found=None;let mut count=0;
 for (i,p) in leaves.iter().enumerate(){if p.first_commitment==cm{found=Some((i,false));count+=1;}if p.second_occupied==M31(1)&&p.second_commitment==cm{found=Some((i,true));count+=1;}}
 (found,count)
}
struct Lane {root:Digest,selected:Option<(PoolV1PairLeafWitnessV1,usize,bool,[Digest;20])>}
fn prepare(v:&Value,cm:Digest)->Result<Lane>{
 let leaves=lane(v)?;let (selected,count)=locate(&leaves,cm);ensure!(count<=1,"duplicate input commitment");let index=selected.map(|x|x.0).unwrap_or(0);
 let (root,siblings)=path(hashes(&leaves)?,index);
 Ok(Lane{root,selected:selected.map(|(i,second)|(leaves[i],i,second,siblings))})
}
fn push_lane(out:Result<Vec<Lane>>,v:&Value,cm:Digest)->Result<Vec<Lane>>{let mut out=out?;out.push(prepare(v,cm)?);Ok(out)}
pub fn input(q:&Value,cm:Digest,k:Digest,salt:Digest,value:u32,anchor:Digest)->Result<PoolV1PairForestInputNoteWitnessV1>{
 let all=q["lane_leaf_sets"].as_array().ok_or_else(||anyhow!("missing complete public lane leaf sets"))?;
 ensure!(all.len()==8,"all eight public lane leaf sets required");
 let mut prepared=Ok(Vec::with_capacity(8));for v in all{prepared=push_lane(prepared,v,cm);}let prepared=prepared?;
 let mut roots:Vec<Digest>=prepared.iter().map(|l|l.root).collect();
 let mut selected=None;let mut matches=0;
 for (l,p) in prepared.iter().enumerate(){if let Some((pair,i,second,siblings))=p.selected{matches+=1;selected=Some((l,pair,i,second,siblings));}}
 ensure!(matches==1,"input commitment must occur in one lane");
 let (l,pair,i,second,siblings)=selected.ok_or_else(||anyhow!("input absent"))?;
 let mut supers=[roots[0];3];let mut directions=[false;3];let mut index=l;
 for level in 0..3{supers[level]=roots[index^1];directions[level]=index%2==1;index>>=1;roots=parent_level(&roots,POOL_V1_PAIR_EMPTY_ROOTS[0]);}
 ensure!(roots[0]==anchor,"complete public leaves do not reconstruct checkpoint");
 Ok(PoolV1PairForestInputNoteWitnessV1{pair:PoolV1PairInputNoteWitnessV1{nullifier_key:k,salt,value,pair_leaf:pair,selected_second:second,membership:PoolV1MembershipWitnessV1{siblings,index:i as u32}},super_root_siblings:supers,super_root_directions:directions})
}
