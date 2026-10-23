#!/usr/bin/env python3
"""Widen the complete native caller context to logical data/lamport Rc counts.
The already-checked RcInner header projection is validated against real SDK
getters before injection. Fields are restored before harness handle destruction.
No frozen source function, child hook, argument assertion or byte query changes.
"""
from pathlib import Path
import json,hashlib,sys
base,out=map(Path,sys.argv[1:3]);(out/'src').mkdir(parents=True,exist_ok=False)
original=(base/'src/lib.rs').read_text();source=original
marker=' let initial_counts:[isize;3]=kani::any();'
assert source.count(marker)==1
source=source.replace(marker,''' // Reuse the pinned RcInner layout from the wider primitive certificates.
 let data_strong=core::array::from_fn::<_,3,_>(|i|unsafe{std::rc::Rc::as_ptr(&data_roots[i]).cast::<usize>().sub(2).cast_mut()});
 let data_weak=core::array::from_fn::<_,3,_>(|i|unsafe{std::rc::Rc::as_ptr(&data_roots[i]).cast::<usize>().sub(1).cast_mut()});
 let lamport_strong=core::array::from_fn::<_,3,_>(|i|unsafe{std::rc::Rc::as_ptr(&lamport_roots[i]).cast::<usize>().sub(2).cast_mut()});
 let lamport_weak=core::array::from_fn::<_,3,_>(|i|unsafe{std::rc::Rc::as_ptr(&lamport_roots[i]).cast::<usize>().sub(1).cast_mut()});
 let original_rc=core::array::from_fn::<_,3,_>(|i|unsafe{[*data_strong[i],*data_weak[i],*lamport_strong[i],*lamport_weak[i]]});
 for i in 0..3 {
  assert_eq!(original_rc[i][0],std::rc::Rc::strong_count(&data_roots[i]));
  assert_eq!(original_rc[i][1],std::rc::Rc::weak_count(&data_roots[i])+1);
  assert_eq!(original_rc[i][2],std::rc::Rc::strong_count(&lamport_roots[i]));
  assert_eq!(original_rc[i][3],std::rc::Rc::weak_count(&lamport_roots[i])+1);
 }
 let rc_counts:[[usize;4];3]=kani::any();
 for i in 0..3 {for j in 0..4 {kani::assume(rc_counts[i][j]>=1 && rc_counts[i][j]<=isize::MAX as usize);}}
 for i in 0..3 {
  unsafe{*data_strong[i]=rc_counts[i][0];*data_weak[i]=rc_counts[i][1];*lamport_strong[i]=rc_counts[i][2];*lamport_weak[i]=rc_counts[i][3];}
  assert_eq!(std::rc::Rc::strong_count(&data_roots[i]),rc_counts[i][0]);
  assert_eq!(std::rc::Rc::weak_count(&data_roots[i]),rc_counts[i][1]-1);
  assert_eq!(std::rc::Rc::strong_count(&lamport_roots[i]),rc_counts[i][2]);
  assert_eq!(std::rc::Rc::weak_count(&lamport_roots[i]),rc_counts[i][3]-1);
 }
'''+marker,1)
marker=' for i in 0..3 {unsafe{(*counters[i]).set(0);(*lamport_counters[i]).set(0);}}'
assert source.count(marker)==1
source=source.replace(marker,''' for i in 0..3 {
  assert_eq!(std::rc::Rc::strong_count(&data_roots[i]),rc_counts[i][0]);
  assert_eq!(std::rc::Rc::weak_count(&data_roots[i]),rc_counts[i][1]-1);
  assert_eq!(std::rc::Rc::strong_count(&lamport_roots[i]),rc_counts[i][2]);
  assert_eq!(std::rc::Rc::weak_count(&lamport_roots[i]),rc_counts[i][3]-1);
 }
'''+marker+'''
 for i in 0..3 {unsafe{
  *data_strong[i]=original_rc[i][0];*data_weak[i]=original_rc[i][1];
  *lamport_strong[i]=original_rc[i][2];*lamport_weak[i]=original_rc[i][3];
 }}''',1)
source=source.replace(' kani::cover!(actual.is_ok(),"native caller accepts with full arbitrary checkpoint bytes");',''' kani::cover!(actual.is_ok(),"native caller accepts with full arbitrary checkpoint bytes");
 kani::cover!(actual.is_ok()&&rc_counts[0][0]==1,"native caller accepts with logical data strong1");
 kani::cover!(actual.is_ok()&&rc_counts[0][0]==isize::MAX as usize,"native caller accepts with logical data strongMAX");''',1)
full='full-usize' in sys.argv[3:]
if full:
 source=source.replace('rc_counts[i][j]>=1 && rc_counts[i][j]<=isize::MAX as usize','rc_counts[i][j]>=1')
 source=source.replace('rc_counts[0][0]==isize::MAX as usize','rc_counts[0][0]==usize::MAX')
 source=source.replace(' kani::cover!(actual.is_ok()&&rc_counts[0][0]==usize::MAX,"native caller accepts with logical data strongMAX");',''' kani::cover!(actual.is_ok()&&rc_counts[0][0]==usize::MAX,"native caller accepts with logical data strongMAX");
 kani::cover!(actual.is_ok()&&rc_counts[0][1]==usize::MAX,"native caller accepts with logical internal weakMAX");''')
prefix=original[:original.index('#[cfg(kani)] mod proofs')];assert source.startswith(prefix)
(out/'src/lib.rs').write_text(source);(out/'Cargo.toml').write_bytes((base/'Cargo.toml').read_bytes())
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(source),base_source_sha256=sha(original),unchanged_source_prefix_sha256=sha(prefix),qualification=__doc__,rc_domain='All twelve data/lamport Rc strong and internal weak fields independently1..isizeMAX; public weak=internal-1. Constructor header layout checked against SDK getters before injection; getter correspondence checked after injection; all four fields per root unchanged after the complete source body, for both returned statuses. Original fields restored before any harness Rc owner is destroyed.',retained='All previous common-child, seeded-prefix/tag, scan, descriptor-alias normalization and runtime/P6/source-instance/ordered-oracle obligations remain. Canonical constructor Rc counts describe only pre-injection harness initialization, not the source-call input domain. No arbitrary runtime heap or whole S2 closure follows.'),indent=2)+'\n')
if full:
 p=out/'source-cut.json';m=json.loads(p.read_text());m['rc_domain']=m['rc_domain'].replace('1..isizeMAX','1..usizeMAX');m['pinned_std_source']='rustc1.93.0-nightly53732d5e0 alloc/src/rc.rs: inc_strong/inc_weak wrap and abort on zero, not at isizeMAX. No artificial upper-half exclusion is retained.';p.write_text(json.dumps(m,indent=2)+'\n')
