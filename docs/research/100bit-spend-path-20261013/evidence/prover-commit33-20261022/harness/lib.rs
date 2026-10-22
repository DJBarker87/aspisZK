extern crate alloc;
use std::cell::Cell;
use std::ops::Index;

// D145 substitute: ordered unique association list, replacement returns old
// value, get and iteration use sorted keys. No std B-tree is linked here.
#[derive(Clone,Debug,PartialEq,Eq)]
struct BTreeMap<K,V>(Vec<(K,V)>);
impl<K:Ord,V> BTreeMap<K,V> {
 fn new()->Self {Self(Vec::new())}
 fn insert(&mut self,k:K,v:V)->Option<V> {
  let mut i=0;
  while i<self.0.len() && self.0[i].0<k {i+=1;}
  if i<self.0.len() && self.0[i].0==k {
   Some(std::mem::replace(&mut self.0[i].1,v))
  } else {self.0.insert(i,(k,v));None}
 }
 fn entry(&mut self,k:K)->Entry<'_,K,V> {Entry(self,k)}
}
impl<K:Ord,V> Index<&K> for BTreeMap<K,V> {
 type Output=V;
 fn index(&self,k:&K)->&V {
  for (key,value) in &self.0 {if key==k {return value;}}
  panic!("absent source index")
 }
}
impl<'a,K,V> IntoIterator for &'a BTreeMap<K,V> {
 type Item=(&'a K,&'a V);
 type IntoIter=std::iter::Map<std::slice::Iter<'a,(K,V)>,fn(&'a (K,V))->(&'a K,&'a V)>;
 fn into_iter(self)->Self::IntoIter {self.0.iter().map(|(k,v)|(k,v))}
}
impl<K,V> IntoIterator for BTreeMap<K,V> {
 type Item=(K,V);type IntoIter=std::vec::IntoIter<(K,V)>;
 fn into_iter(self)->Self::IntoIter {self.0.into_iter()}
}
struct Entry<'a,K,V>(&'a mut BTreeMap<K,V>,K);
impl<'a,K:Ord,V> Entry<'a,K,V> {
 fn or_insert_with(self,f:impl FnOnce()->V)->&'a mut V {
  let mut i=0;
  while i<self.0.0.len() && self.0.0[i].0<self.1 {i+=1;}
  if i==self.0.0.len() || self.0.0[i].0!=self.1 {self.0.0.insert(i,(self.1,f()));}
  &mut self.0.0[i].1
 }
}
#[derive(Clone)] struct Drawn {queries:Vec<u32>}
struct Eval {bytes:[u8;4],calls:Cell<usize>}
struct View {q1:Eval}
fn eval_at(q:&Eval,i:usize)->u8 {q.calls.set(q.calls.get()+1);q.bytes[i%4] ^ i as u8}
fn encoded(v:impl Iterator<Item=u8>)->Vec<u8> {v.collect()}
struct Coins {seed:u8,next:usize}
impl Coins {fn coin(&mut self)->[u8;32] {let x=[self.seed ^ self.next as u8;32];self.next+=1;x}}
#[derive(Debug,PartialEq,Eq)] enum Error {Transcript}
type Table=BTreeMap<Vec<u8>,[u8;32]>;
// This file is generated from exact source spans, without rewriting bodies.
include!("native-loops.rs");

fn folded_rec(q:&[u32],view:&View,mut out:BTreeMap<usize,Vec<u8>>)->BTreeMap<usize,Vec<u8>> {
 if q.is_empty() {return out;}
 let v=q[0] as usize/4;
 if !out.0.iter().any(|(k,_)|*k==v) {
  let bytes=encoded((4*v..4*v+4).map(|i|eval_at(&view.q1,i)));
  out.insert(v,bytes);
 }
 folded_rec(&q[1..],view,out)
}
fn publish_rec(q:&[u32],o:&BTreeMap<usize,(u8,Vec<u8>,Vec<u8>)>,
 l1:&BTreeMap<usize,(Vec<u8>,[u8;32])>,l2:&BTreeMap<usize,(Vec<u8>,[u8;32])>,
 f:&BTreeMap<usize,Vec<u8>>,lf:&BTreeMap<usize,(Vec<u8>,[u8;32])>,mut out:Vec<u8>)->Vec<u8> {
 if q.is_empty(){return out;}
 let u=q[0] as usize;
 for v in [&o[&u].1[..],&o[&u].2[..],&l1[&u].1[..],&l2[&u].1[..],&f[&(u/4)][..],&lf[&(u/4)].1[..]] {out.extend_from_slice(v);}
 publish_rec(&q[1..],o,l1,l2,f,lf,out)
}
fn merge_rec(mut table:Table,reads:&[(Vec<u8>,[u8;32])])->Result<Table,Error> {
 if reads.is_empty() {return Ok(table);}
 let (a,v)=&reads[0];
 let previous=table.insert(a.clone(),*v);
 if previous.map_or(false,|old|old!=*v) {return Err(Error::Transcript);}
 merge_rec(table,&reads[1..])
}
#[cfg(kani)] mod proofs {
 use super::*;
 fn queries()->Drawn {
  let n:usize=kani::any();kani::assume(n<=3);
  let xs:[u8;3]=kani::any();Drawn{queries:xs[..n].iter().map(|x|*x as u32).collect()}
 }
 #[kani::proof] #[kani::unwind(70)]
 fn folded_loop() {
  let drawn=queries();let bytes:[u8;4]=kani::any();
  let a=View{q1:Eval{bytes,calls:Cell::new(0)}};
  let b=View{q1:Eval{bytes,calls:Cell::new(0)}};
  let actual=native_folded(&drawn,&a);let expected=folded_rec(&drawn.queries,&b,BTreeMap::new());
  assert_eq!(actual,expected);assert_eq!(a.q1.calls.get(),b.q1.calls.get());
 }
 #[kani::proof] #[kani::unwind(70)]
 fn leaf_order_and_query_publication() {
  let drawn=queries();let mut opened=BTreeMap::new();let mut folded=BTreeMap::new();
  let cells:[u8;3]=kani::any();
  for (i,&q) in drawn.queries.iter().enumerate() {opened.insert(q as usize,(0,vec![cells[i]],vec![cells[i]^1]));folded.insert(q as usize/4,vec![cells[i]^2]);}
  let seed:u8=kani::any();let mut coins=Coins{seed,next:0};
  let (l1,l2,lf)=native_leaves(&opened,&folded,&mut coins);
  let mut counter=0;
  for (u,(_,c1,c2)) in &opened {
   assert_eq!(l1[u],(c1.clone(),[seed ^ counter as u8;32]));counter+=1;
   assert_eq!(l2[u],(c2.clone(),[seed ^ counter as u8;32]));counter+=1;
  }
  for (v,f) in &folded {assert_eq!(lf[v],(f.clone(),[seed ^ counter as u8;32]));counter+=1;}
  assert_eq!(coins.next,counter);
  assert_eq!(native_publish(&drawn,&opened,&l1,&l2,&folded,&lf),publish_rec(&drawn.queries,&opened,&l1,&l2,&folded,&lf,Vec::new()));
 }
 #[kani::proof] #[kani::unwind(70)]
 fn transcript_merge() {
  let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=2 && m<=2);
  let keys:[u8;4]=kani::any();let vals:[u8;4]=kani::any();
  let mut table=Table::new();let mut transcript=Table::new();
  for i in 0..n {table.insert(vec![keys[i]],[vals[i];32]);}
  for i in 0..m {transcript.insert(vec![keys[2+i]],[vals[2+i];32]);}
  let expected=merge_rec(table.clone(),&transcript.0);
  assert_eq!(native_merge(table,transcript),expected);
 }
}
