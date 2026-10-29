use aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairCopyRowLinkV1 as Link;
use aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairCopyRowLinkKindV1 as Kind;
use aspis_core::field::QM31;
use std::path::{Path,PathBuf};
#[inline(never)] pub fn own_drop_links(v:Vec<Link>){drop(v)}
#[inline(never)] pub fn own_drop_rows(v:Vec<u16>){drop(v)}
#[inline(never)] pub fn own_drop_sparse(v:Vec<(usize,QM31)>){drop(v)}
#[inline(never)] pub fn own_drop_string(v:String){drop(v)}
#[inline(never)] pub fn own_drop_box(v:Box<Link>){drop(v)}
#[inline(never)] pub fn own_drop_array(v:[u16;64]){let _=v;}
#[inline(never)] pub fn own_join(base:&Path,name:String)->PathBuf{base.join(name)}
fn main(){
 assert!(!std::mem::needs_drop::<Link>());
 assert!(!std::mem::needs_drop::<u16>());
 assert!(!std::mem::needs_drop::<(usize,QM31)>());
 assert!(!std::mem::needs_drop::<[u16;64]>());
 println!("link size={} align={} kind={} producer={} consumer={}",std::mem::size_of::<Link>(),std::mem::align_of::<Link>(),std::mem::offset_of!(Link,kind),std::mem::offset_of!(Link,producer_row),std::mem::offset_of!(Link,consumer_row));
 println!("sparse size={} align={}",std::mem::size_of::<(usize,QM31)>(),std::mem::align_of::<(usize,QM31)>());
 for n in [0,1,64,127,136,254,272,1024] {
  let mut rows=Vec::<u16>::with_capacity(n);
  for i in 0..n {rows.push(i as u16)}
  rows.truncate(n/2);assert_eq!(rows.len(),n/2);
  own_drop_rows(std::hint::black_box(rows));
  let links=(0..n).map(|i|Link{kind:Kind::PrivatePathCurrent{level:(i%24)as u8},producer_row:i as u16,consumer_row:(i+1)as u16}).collect::<Vec<_>>();
  own_drop_links(std::hint::black_box(links));
  own_drop_sparse(std::hint::black_box(vec![(0,QM31::ONE);n]));
 }
 own_drop_string(std::hint::black_box("name".repeat(17)));
 own_drop_box(std::hint::black_box(Box::new(Link{kind:Kind::OwnerOutput,producer_row:0,consumer_row:1})));
 own_drop_array(std::hint::black_box([0;64]));
 let joined=own_join(Path::new("base"),std::hint::black_box("name".to_owned()));assert_eq!(joined,PathBuf::from("base/name"));
 println!("finite validation only; compiler/MIR agreement is reclassification within existing tool trust");
}
