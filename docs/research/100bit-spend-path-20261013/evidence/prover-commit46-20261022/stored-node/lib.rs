//! Native callback expression, std indexing governed by D157's exact contract.
use std::ops::Index;
struct Table { key:usize,kids:[[u8;32];2] }
impl Index<&usize> for Table {
 type Output=[[u8;32];2];
 fn index(&self,key:&usize)->&Self::Output {assert_eq!(*key,self.key);&self.kids}
}
// D157 Vec::Index contract projected to the queried depth. Its complete
// list-domain law is named in ProverCommitStdIndex46.TrustedSequence.
struct Children { depth:usize,table:Table }
impl Index<usize> for Children {
 type Output=Table;
 fn index(&self,depth:usize)->&Self::Output {assert_eq!(depth,self.depth);&self.table}
}
struct ProgrammedTree {children:Children}
impl ProgrammedTree {
 fn node(&self,depth:u32,index:u32)->[u8;32] {
  self.children[depth as usize][&(index as usize/2)][index as usize%2]
 }
}
pub fn select(kids:[[u8;32];2],index:u32)->[u8;32] {
 if index&1==0 {kids[0]} else {kids[1]}
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(36)]
 fn stored_node() {
  let depth:u32=kani::any();let index:u32=kani::any();
  kani::assume(depth<18 && index<1<<18);
  let values:[[u8;32];2]=kani::any();
  let children=Children{depth:depth as usize,table:Table{key:index as usize/2,kids:values}};
  let tree=ProgrammedTree{children};
  let actual=tree.node(depth,index);
  let expected=select(values,index);
  assert_eq!(actual,expected);
 }
}
