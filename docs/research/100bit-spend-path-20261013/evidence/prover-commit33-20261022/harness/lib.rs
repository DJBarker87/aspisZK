extern crate alloc;
use std::cell::Cell;
use std::ops::Index;

// D145 substitute: ordered unique association list, replacement returns old
// value, get and iteration use sorted keys. No std B-tree is linked here.
#[derive(Clone,Debug,PartialEq,Eq)]
struct BTreeMap<K,V> { entries:[Option<(K,V)>;4], len:usize }
impl<K:Ord,V> BTreeMap<K,V> {
 fn new()->Self {Self{entries:[None,None,None,None],len:0}}
 fn position(&self,k:&K)->usize {
  let mut i=0;while i<self.len && self.entries[i].as_ref().unwrap().0<*k {i+=1;}i
 }
 fn insert(&mut self,k:K,v:V)->Option<V> {
  let i=self.position(&k);
  if i<self.len && self.entries[i].as_ref().unwrap().0==k {
   self.entries[i].replace((k,v)).map(|(_,old)|old)
  } else {
   assert!(self.len<4);let mut j=self.len;
   while j>i {self.entries[j]=self.entries[j-1].take();j-=1;}
   self.entries[i]=Some((k,v));self.len+=1;None
  }
 }
 fn entry(&mut self,k:K)->Entry<'_,K,V> {Entry(self,k)}
}
impl<K:Ord,V> Index<&K> for BTreeMap<K,V> {
 type Output=V;
 fn index(&self,k:&K)->&V {
  let i=self.position(k);assert!(i<self.len);
  let (key,v)=self.entries[i].as_ref().unwrap();assert!(key==k);v
 }
}
struct MapIter<'a,K,V> {map:&'a BTreeMap<K,V>,at:usize}
impl<'a,K,V> Iterator for MapIter<'a,K,V> {
 type Item=(&'a K,&'a V);
 fn next(&mut self)->Option<Self::Item> {
  if self.at==self.map.len {return None;}
  let (k,v)=self.map.entries[self.at].as_ref().unwrap();self.at+=1;Some((k,v))
 }
}
impl<'a,K,V> IntoIterator for &'a BTreeMap<K,V> {
 type Item=(&'a K,&'a V);type IntoIter=MapIter<'a,K,V>;
 fn into_iter(self)->Self::IntoIter {MapIter{map:self,at:0}}
}
struct MapIntoIter<K,V> {map:BTreeMap<K,V>,at:usize}
impl<K,V> Iterator for MapIntoIter<K,V> {
 type Item=(K,V);
 fn next(&mut self)->Option<Self::Item> {
  if self.at==self.map.len {return None;}
  let entry=self.map.entries[self.at].take();self.at+=1;entry
 }
}
impl<K,V> IntoIterator for BTreeMap<K,V> {
 type Item=(K,V);type IntoIter=MapIntoIter<K,V>;
 fn into_iter(self)->Self::IntoIter {MapIntoIter{map:self,at:0}}
}
struct Entry<'a,K,V>(&'a mut BTreeMap<K,V>,K);
impl<'a,K:Ord,V> Entry<'a,K,V> {
 fn or_insert_with(self,f:impl FnOnce()->V)->&'a mut V {
  let i=self.0.position(&self.1);
  if i==self.0.len || self.0.entries[i].as_ref().unwrap().0!=self.1 {
   self.0.insert(self.1,f());
  }
  &mut self.0.entries[i].as_mut().unwrap().1
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
 if !(&out).into_iter().any(|(k,_)|*k==v) {
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
 #[kani::proof] #[kani::unwind(8)]
 fn folded_loop() {
  // Single source-loop transition from an arbitrary bounded invariant state.
  let query:u8=kani::any();let drawn=Drawn{queries:vec![query as u32]};
  let bytes:[u8;4]=kani::any();let mut initial=BTreeMap::new();
  let old_key:u8=kani::any();let old:[u8;4]=kani::any();let present:bool=kani::any();
  if present {initial.insert(old_key as usize,old.to_vec());}
  let a=View{q1:Eval{bytes,calls:Cell::new(0)}};
  let b=View{q1:Eval{bytes,calls:Cell::new(0)}};
  let actual=native_folded(&drawn,&a,initial.clone());
  let expected=folded_rec(&drawn.queries,&b,initial);
  assert!(actual==expected);assert!(a.q1.calls.get()==b.q1.calls.get());
 }
 #[kani::proof] #[kani::unwind(8)]
 fn leaf_order_and_query_publication() {
  let drawn=queries();let mut opened=BTreeMap::new();let mut folded=BTreeMap::new();
  let cells:[u8;3]=kani::any();
  for (i,&q) in drawn.queries.iter().enumerate() {opened.insert(q as usize,(0,vec![cells[i]],vec![cells[i]^1]));folded.insert(q as usize/4,vec![cells[i]^2]);}
  let seed:u8=kani::any();let mut coins=Coins{seed,next:0};
  let (l1,l2,lf)=native_leaves(&opened,&folded,&mut coins);
  let mut counter=0;
  for (u,(_,c1,c2)) in &opened {
   assert!(l1[u]==(c1.clone(),[seed ^ counter as u8;32]));counter+=1;
   assert!(l2[u]==(c2.clone(),[seed ^ counter as u8;32]));counter+=1;
  }
  for (v,f) in &folded {assert!(lf[v]==(f.clone(),[seed ^ counter as u8;32]));counter+=1;}
  assert!(coins.next==counter);
  let actual=native_publish(&drawn,&opened,&l1,&l2,&folded,&lf);
  let expected=publish_rec(&drawn.queries,&opened,&l1,&l2,&folded,&lf,Vec::new());
  assert!(actual.len()==expected.len());
  let at:usize=kani::any();
  if at<actual.len() {assert!(actual[at]==expected[at]);}
 }
 #[kani::proof] #[kani::unwind(8)]
 fn transcript_merge() {
  let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=2 && m<=2);
  let keys:[u8;4]=kani::any();let vals:[u8;4]=kani::any();
  let mut table=Table::new();let mut transcript=Table::new();
  for i in 0..n {table.insert(vec![keys[i]],[vals[i];32]);}
  for i in 0..m {transcript.insert(vec![keys[2+i]],[vals[2+i];32]);}
  let reads:Vec<_>=transcript.clone().into_iter().collect();
  let expected=merge_rec(table.clone(),&reads);
  assert!(native_merge(table,transcript)==expected);
 }
}
