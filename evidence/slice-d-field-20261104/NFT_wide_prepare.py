from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-core/src/';n=C+'field/wide_exact.rs'
old=subprocess.check_output(['git','show','4bb3b3f:'+n],cwd=R,text=True);s=old
s=s.replace('pub fn new(c0: QM31, c1: QM31) -> Self','#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| NFT_wide::new_matches(r,c0,c1) != cfg!(NFT_invert)))]\npub fn new(c0: QM31, c1: QM31) -> Self',1)
s=s.replace('pub fn neg(self) -> Self','#[cfg_attr(kani,kani::requires(NFT_wide::canonical(self)))]\n#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| NFT_wide::neg_matches(r,self) != cfg!(NFT_invert)))]\npub fn neg(self) -> Self',1)
s+='\n#[cfg(kani)]\n#[path="NFT_wide.rs"]\nmod NFT_wide;\n'
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn any_e()->WideExact{WideExact{c0:any_q(),c1:any_q()}}
fn new_q(r:QM31,v:QM31)->bool{r.c0.a.0==v.c0.a.0%P && r.c0.b.0==v.c0.b.0%P && r.c1.a.0==v.c1.a.0%P && r.c1.b.0==v.c1.b.0%P}
pub(super) fn new_matches(r:&WideExact,c0:QM31,c1:QM31)->bool{new_q(r.c0,c0) && new_q(r.c1,c1)}
fn cq(v:QM31)->bool{v.c0.a.0<P && v.c0.b.0<P && v.c1.a.0<P && v.c1.b.0<P}
pub(super) fn canonical(v:WideExact)->bool{cq(v.c0)&&cq(v.c1)}
fn nw(x:u32)->u32{if x==0{0}else{P-x}}
fn neg_q(r:QM31,v:QM31)->bool{r.c0.a.0==nw(v.c0.a.0)&&r.c0.b.0==nw(v.c0.b.0)&&r.c1.a.0==nw(v.c1.a.0)&&r.c1.b.0==nw(v.c1.b.0)}
pub(super) fn neg_matches(r:&WideExact,v:WideExact)->bool{neg_q(r.c0,v.c0)&&neg_q(r.c1,v.c1)}
#[kani::proof_for_contract(WideExact::new)]
KMXL
fn new_contract(){let _=WideExact::new(any_q(),any_q());}
#[kani::proof_for_contract(WideExact::neg)]
KMXL
fn neg_contract(){let v=any_e();kani::assume(canonical(v));let _=v.neg();}
#[kani::proof]
KMXL
fn copy_positive(){let src=any_e();let mut dst=any_e();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(dst.c0.c0.a.0==src.c0.c0.a.0&&dst.c1.c1.b.0==src.c1.c1.b.0);}
#[kani::proof]
KMXL
fn copy_negative(){let src=any_e();let mut dst=any_e();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(dst.c1.c1.b.0!=src.c1.c1.b.0);}
'''.replace('KMXL','''#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]''')
# P/CM31/M31 are imported by the parent in the frozen source.
code=code.replace('use super::*;','use super::*;\nuse crate::field::{CM31,M31,P};')
files={n:s,C+'field/NFT_wide.rs':code};inputs=json.loads((E/'NFT_NATIVE_INPUTS.json').read_text());inputs.update(files);(E/'NFT_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n');pins=json.loads((E/'NFT_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in files.items()});(E/'NFT_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in files.items():patch+=difflib.unified_diff((old if n.endswith('wide_exact.rs')else '').splitlines(True),t.splitlines(True),fromfile='a/'+n if n.endswith('wide_exact.rs')else '/dev/null',tofile='b/'+n)
(E/'NFT_wide.patch').write_text(''.join(patch))
