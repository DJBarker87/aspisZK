"""Instrument unchanged source arithmetic statements and owned stores.
This produces finite-validation traces, never a universal source binding.
"""
from pathlib import Path
import json,re,hashlib
T=Path('tools/pv-b3p6-20261028');P=T/'v244-matrix13';P.mkdir(exist_ok=True)
manifest=(T/'v244-fidelity/Cargo.toml').read_text();manifest=manifest[:manifest.index('[[bin]]')]+manifest[manifest.index('[dependencies]'):]
manifest+='\n[[bin]]\nname="matrix13"\npath="main.rs"\n';(P/'Cargo.toml').write_text(manifest);(P/'Cargo.lock').write_bytes((T/'v244-fidelity/Cargo.lock').read_bytes())
def body(s,name):
 a=re.search(r'\b(?:pub(?:\([^)]*\))?\s+)?fn '+name+r'\b',s).start();b=s.index('{',a);d=1;i=b+1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
original=body(Path('crates/aspis-core/src/field.rs').read_text(),'qm31_sum_products3_prepared'); owned=(T/'v244/reference_field.rs').read_text();acc=body(owned,'accumulate_prepared227')
# Preserve every original arithmetic statement; append observation after its store.
prefix=original[original.index('{')+1:original.rindex('qm31_from_karatsuba_channel_sums')]
store='''sums[component][channel] += left[index].components[component][channel].0 as u64
                    * right_components[component][channel].0 as u64;'''
assert prefix.count(store)==1
src=prefix.replace(store,store+'\n                trace.push(sums);')
source_fn='''pub fn source_trace13(left:&[PreparedQm31Multiplier;3],right:&[QM31;3])->Vec<[[u64;3];3]> {
 let mut trace=Vec::new();
'''+src+'\ntrace\n}\n'
# Nine immutable store expressions, each instrumented without alteration.
traced=acc.replace('fn accumulate_prepared227','fn traced_accumulate13').replace(')->[[u64;3];3]',',trace:&mut Vec<[[u64;3];3]>)->[[u64;3];3]')
assert traced!=acc
traced,n=re.subn(r'(sums\[\d\]\[\d\]\s*\+=.*?;)',r'\1 trace.push(sums);',traced);assert n==9
wrapper='''pub fn owned_trace13(left:&[PreparedQm31Multiplier;3],right:&[QM31;3])->Vec<[[u64;3];3]> {
 let mut sums=[[0u64;3];3];let mut trace=Vec::new();
 sums=traced_accumulate13(sums,right[0],left[0],&mut trace);
 sums=traced_accumulate13(sums,right[1],left[1],&mut trace);
 let _=traced_accumulate13(sums,right[2],left[2],&mut trace);trace
}
'''
(P/'reference_field.rs').write_text(owned+'\n'+source_fn+'\n'+traced+'\n'+wrapper)
(P/'main.rs').write_text('''use aspis_core::field::{M31,CM31,QM31,P};
mod reference_field;
fn q(n:u32)->QM31 {QM31{c0:CM31{a:M31(n),b:M31(n.rotate_left(7))},c1:CM31{a:M31(n.rotate_left(13)),b:M31(n.rotate_left(23))}}}
fn main(){
 assert!(!cfg!(debug_assertions));
 assert!(!std::mem::needs_drop::<std::ops::Range<usize>>());
 assert!(!std::mem::needs_drop::<std::ops::RangeInclusive<usize>>());
 assert!(!std::mem::needs_drop::<[QM31;3]>());
 assert!(!std::mem::needs_drop::<[[u64;3];3]>());
 let negative=std::env::args().any(|a|a=="--negative");
 let seeds=[0,1,7,19,P-1,P,P+1,u32::MAX,0x80000000,0xabcdef01];
 let mut entries=0usize;let mut changed=0usize;
 for (case,seed) in seeds.into_iter().enumerate(){
  let l:[QM31;3]=core::array::from_fn(|i|q(seed.wrapping_add((i as u32).wrapping_mul(131))));
  let r=core::array::from_fn(|i|q(seed.wrapping_add((i as u32).wrapping_mul(173))));
  let left=core::array::from_fn(|i|reference_field::PreparedQm31Multiplier::new(l[i]));
  let native_left=core::array::from_fn(|i|aspis_core::field::PreparedQm31Multiplier::new(l[i]));
  let native=aspis_core::field::qm31_sum_products3_prepared(&native_left,&r);
  let reference=reference_field::qm31_sum_products3_prepared(&left,&r);
  assert_eq!(native,reference,"final result case {case}");
  let source=reference_field::source_trace13(&left,&r);
  let mut owned=reference_field::owned_trace13(&left,&r);
  assert_eq!(source.len(),27);assert_eq!(owned.len(),27);
  if negative { owned[26][2][2]^=1; }
  for step in 0..27 {for c in 0..3 {for k in 0..3 {
   assert_eq!(source[step][c][k],owned[step][c][k],"matrix case {case} step {step} cell {c},{k}");entries+=1;
  }}}
  if source[26]!=[[0u64;3];3] {changed+=1;}
 }
 assert!(changed>0);
 println!("cases=10 store_snapshots=270 matrix_entries_compared={entries} changed_cases={changed} final_deployed_results=10 needs_drop_false=4");
}
''')
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(Path('evidence/pv-b3p6-20261028/resume13')/'matrix-instrumentation.json').write_text(json.dumps(dict(original_body_sha256=sha(original),owned_accumulator_body_sha256=sha(acc),source_prefix_sha256=sha(prefix),source_store_instrumentation_count=1,owned_store_instrumentation_count=n,source_statements_unchanged_after_erasing_observations=src.replace('\n                trace.push(sums);','')==prefix,source_type_adapter='uses owned PreparedQm31Multiplier components; identical constructor layout/formula; actual deployed final result independently compared for every case',evidence_class='finite validation of instrumented exact source arithmetic prefix and owned stores; NOT a universal binding or a deployed internal-state observation',cases='10 fixed seeds including noncanonical u32 values; 27 stores × 9 cells × 10 cases'),indent=2)+'\n')
