"""Exact frozen source windows, not an extractor or a substitute Lean body."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs'
src=subprocess.check_output(['git','show',rev+':'+path],text=True)
body=src[src.index('fn external_local_packed_raw('):];body=body[:body.index('\n#[inline(always)]')]
start=body.index('            let a = u64::from(input[0][limb]);');end=body.index('\n        })',start);cell=body[start:end]
start=body.index('    let bound = EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;');suffix=body[start:body.rindex('\n}')]
scan='''            all_local_limbs_bounded &= local[output][limb] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            limb += 1;''';assert scan in body
refpath='evidence/native-front2-20261028/NDE_E011/sources/NDE_reference.rs';ref=subprocess.check_output(['git','show','HEAD:'+refpath],text=True)
assert all('fn '+f in ref for f in ['matrix_cell_ref','scan_step_ref','packed_after_ref'])
(E/'NIH_NDE_reference.rs.txt').write_text(ref)
out='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="NIH_NDE_reference.rs"] mod reference;
fn NIH_matrix_window(input:[QM31;4],output:usize,limb:usize,mut table:[[u64;4];4])->[[u64;4];4]{
 let input=input.map(extension_limbs);
 let value={
'''+cell+'''
 };
 table[output][limb]=value;table
}
fn NIH_scan_step(local:[[u64;4];4],mut all_local_limbs_bounded:bool,mut output:usize,mut limb:usize)->(bool,usize,usize,bool){
 if limb<4{
'''+scan+'''
 (all_local_limbs_bounded,output,limb,false)
 }else{output+=1;(all_local_limbs_bounded,output,limb,true)}
}
fn NIH_packed_suffix(local:[[u64;4];4])->[u64;4]{
'''+suffix+'''
}
'''
out+='''fn NIH_input()->[QM31;4]{let raw:[[u32;4];4]=kani::any();
 kani::assume('''+'&&'.join('raw[%d][%d]<2147483647'%(r,j) for r in range(4) for j in range(4))+''');
 raw.map(|x|QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}})}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NDE_matrix_cell(){
 let input=NIH_input();let before:[[u64;4];4]=kani::any();let row:usize=kani::any();let limb:usize=kani::any();kani::assume(row<4&&limb<4);
 let field=|q:QM31|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0][limb];
 let expected=reference::matrix_cell_ref(field(input[0]),field(input[1]),field(input[2]),field(input[3]),row);
 let after=NIH_matrix_window(input,row,limb,before);
 let r:usize=kani::any();let j:usize=kani::any();kani::assume(r<4&&j<4);
 assert_eq!(after[r][j],if r==row&&j==limb{expected ^ if cfg!(NIH_invert){1}else{0}}else{before[r][j]});
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NDE_scan_cell(){
 let table:[[u64;4];4]=kani::any();let flag:bool=kani::any();let row:usize=kani::any();let limb:usize=kani::any();kani::assume(row<4&&limb<=4);
 let cell=if limb<4{table[row][limb]}else{0};let expected=reference::scan_step_ref(flag,cell,7*2147483647,row,limb);
 let out=NIH_scan_step(table,flag,row,limb);
 assert_eq!(out.0,expected.0 ^ cfg!(NIH_invert));assert_eq!(out.1,expected.1);assert_eq!(out.2,expected.2);assert_eq!(out.3,expected.3);
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NDE_packed_after(){
 let table:[[u64;4];4]=kani::any();
 kani::assume('''+'&&'.join('table[%d][%d]<7*2147483647'%(r,j) for r in range(4) for j in range(4))+''');
 let k:usize=kani::any();kani::assume(k<4);
 let expected=reference::packed_after_ref(table,7*2147483647);
 let out=NIH_packed_suffix(table);
 assert_eq!(out[k],expected[k] ^ if cfg!(NIH_invert){1}else{0});
}
'''
(E/'NIH_NDE_poseidon.rs.txt').write_text(out)
(E/'NIH_PACKED_ERASURE.json').write_text(json.dumps(dict(frozen_revision=rev,path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),matrix_window_sha256=hashlib.sha256(cell.encode()).hexdigest(),scan_step_sha256=hashlib.sha256(scan.encode()).hexdigest(),suffix_sha256=hashlib.sha256(suffix.encode()).hexdigest(),reference_path=refpath,reference_sha256=hashlib.sha256(ref.encode()).hexdigest(),method='exact frozen closure expression, one native scan iteration, exact suffix; local records and arbitrary prestate/frame; original harness names retained; no writable static'),indent=2)+'\n')
