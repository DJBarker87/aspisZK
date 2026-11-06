from pathlib import Path
p=Path(__file__).resolve().parent/'NKJ_segments.rs.txt';s=p.read_text()
s+='''
// S: exact selected M31 word, before product cut P, arbitrary cache and indices.
#[kani::requires(i<3&&j<3)]
#[kani::ensures(|out| if cfg!(NKJ_invert) {*out!=cache[i][j].0}else{*out==cache[i][j].0})]
fn NKJ_select_segment(cache:[[M31;3];3],i:usize,j:usize)->u32 {cache[i][j].0}
#[kani::proof_for_contract(NKJ_select_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_select_contract(){let w:[[u32;3];3]=kani::any();let c=[[M31(w[0][0]),M31(w[0][1]),M31(w[0][2])],[M31(w[1][0]),M31(w[1][1]),M31(w[1][2])],[M31(w[2][0]),M31(w[2][1]),M31(w[2][2])]];NKJ_select_segment(c,kani::any(),kani::any());}
fn NKJ_range_ref(start:usize)->[usize;3] {if start<3 {[1,start,start+1]}else{[0,0,start]}}
// I: one actual Range::next; all active and exhausted arms, arbitrary pre-state.
#[kani::ensures(|out| if cfg!(NKJ_invert) {*out!=NKJ_range_ref(start)}else{*out==NKJ_range_ref(start)})]
fn NKJ_range_segment(start:usize)->[usize;3] {let mut r=start..3;let v=r.next();match v {Some(i)=>[1,i,r.start],None=>[0,0,r.start]}}
#[kani::proof_for_contract(NKJ_range_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_range_contract(){NKJ_range_segment(kani::any());}
// Outer while increment, where the frozen guard has established index<N<=4.
#[kani::requires(index<n&&n>=2&&n<=4)]
#[kani::ensures(|out| if cfg!(NKJ_invert) {*out!=index+1}else{*out==index+1})]
fn NKJ_increment_segment(mut index:usize,n:usize)->usize {index+=1;index}
#[kani::proof_for_contract(NKJ_increment_segment)]
fn NKJ_increment_contract(){NKJ_increment_segment(kani::any(),kani::any());}
'''
for shape,ty,zero,cell in [('word_cache','[[u32;3];3]','[[0u32;3];3]','[0][0]'),('range','[usize;3]','[0usize;3]','[0]')]:
 s+=f'''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_{shape}_copy(){{let s:{ty}=kani::any();let mut d={zero};d.copy_from_slice(&s);assert!(if cfg!(NKJ_invert){{d{cell}!=s{cell}}}else{{d{cell}==s{cell}}});}}
#[kani::ensures(|out| if cfg!(NKJ_invert){{out{cell}!=out{cell}}}else{{out{cell}==out{cell}}})]
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
p.write_text(s);print('NKJ arbitrary-index and actual Range::next segments prepared')
