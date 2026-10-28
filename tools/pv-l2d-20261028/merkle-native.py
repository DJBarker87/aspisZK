"""Exact native body freeze + independent finite read-plan differential.
No implementations under crates/ are changed. Not a universal native bridge.
"""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
mp=R/'crates/aspis-r1-cost-probe/src/multiproof.rs';ht=R/'crates/aspis-r1-cost-probe/src/host_tree.rs'
def body(s,start):
 a=s.index(start);b=s.index('{',a);depth=1;i=b+1
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 return s[a:i]
ms=mp.read_text();hs=ht.read_text();rows=[]
def freeze(p,s,start,changes=()):
 b=body(s,start);r=b
 for a,z in changes:r=r.replace(a,z)
 rows.append(dict(path=str(p.relative_to(R)),start=start,body_sha256=hashlib.sha256(b.encode()).hexdigest(),nominal_changes=list(changes)))
 return r
parts=['use std::vec::Vec; const LEAF_BITS:u32=18; const MAX_BATCH:usize=16; #[derive(Clone,Copy)] enum Arity { Two,Eight }']
parts += [freeze(mp,ms,'impl Arity {')]
parts += [freeze(mp,ms,'fn well_formed('),freeze(mp,ms,'fn index_at(')]
parts += [freeze(mp,ms,'pub fn node_count(', [('node_count','generic_count')])]
parts += [freeze(mp,ms,'pub fn generate(', [('node_count','generic_count')])]
parts += ['struct BinaryTree {levels:Vec<Vec<[u8;32]>>}', 'impl BinaryTree {\n'+freeze(ht,hs,'pub(crate) fn multiproof(', [('node_count','host_count')])+'\n}']
for name in ['multiproof_levels','multiproof_level','multiproof_child','check_indices','count_levels','count_level','count_parent']:
 parts.append(freeze(ht,hs,'fn '+name+'('))
parts += [freeze(ht,hs,'fn node_count(', [('node_count','host_count')])]
parts += [r'''
fn address(depth:u32,index:u32)->[u8;32] {
 let mut a=[0;32];a[0]=depth as u8;
 a[1..5].copy_from_slice(&index.to_le_bytes());a
}
fn reference(mut indices:Vec<u32>,levels:u32)->Vec<(u32,u32)> {
 let mut reads=vec![];
 for depth in 0..levels {
  let mut next=vec![];let mut i=0;
  while i<indices.len() {
   let x=indices[i];let parent=x/2;
   let mut end=i+1;
   while end<indices.len()&&indices[end]/2==parent {end+=1;}
   if end-i==1 {reads.push((depth,if x%2==0 {x+1} else {x-1}));}
   next.push(parent);i=end;
  }
  indices=next;
 }
 reads
}
fn check(tree:&BinaryTree,indices:&[u32])->usize {
 let expected=reference(indices.to_vec(),18);let mut calls=vec![];
 let got=generate(Arity::Two,indices,|d,i|{calls.push((d,i));address(d,i)}).unwrap();
 assert_eq!(calls,expected);
 let bytes:Vec<u8>=expected.iter().flat_map(|&(d,i)|address(d,i)).collect();
 assert_eq!(got,bytes);assert_eq!(tree.multiproof(indices).unwrap(),bytes);
 assert_eq!(generic_count(Arity::Two,indices),Some(expected.len()));
 assert_eq!(host_count(indices),Some(expected.len()));1
}
fn main() {
 let tree=BinaryTree{levels:(0..=18).map(|depth|(0..(1u32<<(18-depth))).map(|index|address(depth,index)).collect()).collect()};
 let mut checks=0;
 // Every nonempty subset of sixteen nearby leaves, with all sharing patterns.
 for mask in 1..(1u32<<16) {
  let idx:Vec<u32>=(0..16).filter(|i|mask&(1u32<<i)!=0).collect();
  checks+=check(&tree,&idx);
 }
 let mut state=0x7654_3210_fedc_ba98u64;
 for case in 0..10000 {
  let len=1+case%16;let mut idx=vec![];
  while idx.len()<len {
   state^=state<<13;state^=state>>7;state^=state<<17;
   let x=(state as u32)&((1<<18)-1);
   if !idx.contains(&x) {idx.push(x);}
  }
  idx.sort();checks+=check(&tree,&idx);
 }
 for bad in [vec![],vec![0,0],vec![1,0],vec![1<<18],(0..17).collect()] {
  assert!(generate(Arity::Two,&bad,|_,_|panic!("invalid input reached payload")).is_none());
  assert!(tree.multiproof(&bad).is_none());
 }
 // Exercise generic eight-way branch as a separate finite control.
 let mut eight=0;
 for idx in [vec![0],vec![0,1],vec![0,7,8,63,64,262143]] {
  let mut reads=vec![];
  let got=generate(Arity::Eight,&idx,|d,i|{reads.push((d,i));address(d,i)}).unwrap();
  assert_eq!(got.len(),32*reads.len());assert_eq!(generic_count(Arity::Eight,&idx),Some(reads.len()));eight+=1;
 }
 println!("{{\"binary_inputs\":{},\"eight_way_controls\":{},\"invalid_controls\":5,\"failed\":0}}",checks,eight);
}
''']
p=R/'tools/pv-l2d-20261028/merkle-native.rs';p.write_text('\n\n'.join(parts)+'\n')
(E/'merkle-native-freeze.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),bodies=rows,harness_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),evidence_class='finite native validation preparation; source bodies exact except listed name changes',limitations=['not extraction','not a universal native law','no payload-independence inference from random payloads alone','binary plan Lean model not yet structurally bound']),indent=2)+'\n')
print('frozen bodies',len(rows),'harness bytes',p.stat().st_size)
