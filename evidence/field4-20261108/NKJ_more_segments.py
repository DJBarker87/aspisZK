from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NKJ_segments.rs.txt';s=p.read_text()
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/field.rs'],text=True)
a=frozen.index('    let left_sum = left.c0.add(left.c1);',frozen.index('fn qm31_accumulate_product_channels'));b=frozen.index('    for component in 0..3 {',a);pre=frozen[a:b]
s+='''
fn NKJ_qwords(q:QM31)->[u32;4] {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn NKJ_canonical(q:QM31)->bool {q.c0.a.0<P&&q.c0.b.0<P&&q.c1.a.0<P&&q.c1.b.0<P}
fn NKJ_decode(c:[[M31;3];3])->[[u32;3];3] {[[c[0][0].0,c[0][1].0,c[0][2].0],[c[1][0].0,c[1][1].0,c[1][2].0],[c[2][0].0,c[2][1].0,c[2][2].0]]}
fn NKJ_cache_ref(l:QM31,r:QM31)->[[[u32;3];3];2] {[NKJ_channels(NKJ_qwords(l)),NKJ_channels(NKJ_qwords(r))]}
#[kani::requires(NKJ_canonical(left)&&NKJ_canonical(right))]
#[kani::ensures(|out| if cfg!(NKJ_invert) {*out!=NKJ_cache_ref(left,right)}else{*out==NKJ_cache_ref(left,right)})]
fn NKJ_cache_segment(left:QM31,right:QM31)->[[[u32;3];3];2] {
'''+pre+'''    [NKJ_decode(left_components),NKJ_decode(right_components)]
}
fn NKJ_any_q()->QM31 {let w:[u32;4]=kani::any();QM31 {c0:CM31 {a:M31(w[0]),b:M31(w[1])},c1:CM31 {a:M31(w[2]),b:M31(w[3])}}}
#[kani::proof_for_contract(NKJ_cache_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_cache_contract(){NKJ_cache_segment(NKJ_any_q(),NKJ_any_q());}
type NKJ_Sums=[[u64;3];3];
fn NKJ_write_ref(s:NKJ_Sums,i:usize,j:usize,v:u64)->NKJ_Sums {
'''
rows=[]
for i in range(3):rows.append('['+','.join(f'if i=={i}&&j=={j} {{v}}else{{s[{i}][{j}]}}' for j in range(3))+']')
s+=' ['+','.join(rows)+']\n}\n'
s+='''#[kani::requires(i<3&&j<3)]
#[kani::ensures(|out| if cfg!(NKJ_invert) {*out!=NKJ_write_ref(s,i,j,v)}else{*out==NKJ_write_ref(s,i,j,v)})]
fn NKJ_write_segment(mut s:NKJ_Sums,i:usize,j:usize,v:u64)->NKJ_Sums {s[i][j]=v;s}
#[kani::proof_for_contract(NKJ_write_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_write_contract(){NKJ_write_segment(kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_sums_copy(){let s:NKJ_Sums=kani::any();let mut d=[[0u64;3];3];d.copy_from_slice(&s);let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!(if cfg!(NKJ_invert){d[i][j]!=s[i][j]}else{d[i][j]==s[i][j]});}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_cache_copy(){let s:[[[u32;3];3];2]=kani::any();let mut d=[[[0u32;3];3];2];d.copy_from_slice(&s);let k:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(k<2&&i<3&&j<3);assert!(if cfg!(NKJ_invert){d[k][i][j]!=s[k][i][j]}else{d[k][i][j]==s[k][i][j]});}
'''
for shape,ty,cell in [('sums','NKJ_Sums','[0][0]'),('cache','[[[u32;3];3];2]','[0][0][0]')]:
 s+=f'''#[kani::ensures(|out| if cfg!(NKJ_invert) {{out{cell}!=out{cell}}}else{{out{cell}==out{cell}}})]
#[kani::modifies()]
fn NKJ_weak_{shape}(s:{ty},frame:&mut u8)->{ty} {{if cfg!(NKJ_modifies_bad){{*frame=1;}}s}}
#[kani::proof_for_contract(NKJ_weak_{shape})]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_{shape}_weak_contract(){{let mut f=0;NKJ_weak_{shape}(kani::any(),&mut f);}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_{shape}_real_assert(){{let s:{ty}=kani::any();let mut f=0;let o=NKJ_weak_{shape}(s,&mut f);assert!(o{cell}==s{cell});}}
#[kani::proof]
#[kani::stub_verified(NKJ_weak_{shape})]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_{shape}_unimplied(){{let s:{ty}=kani::any();let mut f=0;let o=NKJ_weak_{shape}(s,&mut f);assert!(o{cell}==s{cell});}}
'''
p.write_text(s)
(E/'NKJ_SOURCE_SEGMENT_PINS.json').write_text(json.dumps(dict(frozen_source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),prelude_start=a,prelude_end=b,prelude_sha256=hashlib.sha256(pre.encode()).hexdigest(),native_harness_sha256=hashlib.sha256(s.encode()).hexdigest()),indent=2))
print('NKJ cache/write cuts and per-shape controls generated from frozen source')
