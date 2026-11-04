from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-core/src/';n=C+'field/wide_exact.rs'
base=subprocess.check_output(['git','show','4bb3b3f:'+n],cwd=R,text=True);s=base
for member in ['c0','c1']:
 sig='pub const fn '+member+'(self) -> QM31';assert s.count(sig)==1
 s=s.replace(sig,'#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| (*r == self.'+member+') != cfg!(NFQ_invert)))]\n'+sig,1)
s+='\n#[cfg(kani)]\n#[path="NFQ_wide.rs"]\nmod NFQ_wide;\n'
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_q()->QM31{QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_wide()->WideExact{WideExact{c0:any_q(),c1:any_q()}}
#[kani::proof_for_contract(WideExact::c0)]
KMXL
fn c0_contract(){let _=any_wide().c0();}
#[kani::proof_for_contract(WideExact::c1)]
KMXL
fn c1_contract(){let _=any_wide().c1();}
#[kani::proof]
KMXL
fn copy_positive(){let src=any_wide();let mut dst=any_wide();let qs=any_q();let mut qd=any_q();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1);core::ptr::copy_nonoverlapping(&qs,&mut qd,1)};assert!(src==dst&&qs==qd);}
#[kani::proof]
KMXL
fn copy_negative(){let src=any_wide();let mut dst=any_wide();let qs=any_q();let mut qd=any_q();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1);core::ptr::copy_nonoverlapping(&qs,&mut qd,1)};assert!(!(src==dst&&qs==qd));}
'''
kmx='''#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]
''';code=code.replace('KMXL',kmx)
files={n:s,C+'field/NFQ_wide.rs':code};inputs=json.loads((E/'NFQ_NATIVE_INPUTS.json').read_text());inputs.update(files);(E/'NFQ_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NFQ_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for path,s in files.items():patch+=difflib.unified_diff(base.splitlines(True) if path==n else [],s.splitlines(True),fromfile='a/'+path if path==n else '/dev/null',tofile='b/'+path)
(E/'NFQ_wide.patch').write_text(''.join(patch))
