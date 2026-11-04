from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-core/src/'
base=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+C+'field.rs'],cwd=R,text=True);s=base
items=[('pub fn neg(self) -> M31', 'r.0 == NFQ_field::neg_ref(self.0)','#[cfg_attr(kani, kani::requires(self.0 < P))]\n'),('pub fn from_m31(a: M31) -> CM31','(r.a.0,r.b.0) == NFQ_field::cm_ref(a.0)',''),('pub fn from_cm31(c0: CM31) -> QM31','(r.c0.a.0,r.c0.b.0,r.c1.a.0,r.c1.b.0) == NFQ_field::qm_ref(c0.a.0,c0.b.0)','')]
for signature,expr,req in items:
 assert s.count(signature)==1
 s=s.replace(signature,req+'#[cfg_attr(kani, kani::modifies())]\n#[cfg_attr(kani, kani::ensures(|r| ('+expr+') != cfg!(NFQ_invert)))]\n'+signature,1)
s+='\n#[cfg(kani)]\n#[path="NFQ_field.rs"]\nmod NFQ_field;\n'
code='''use super::*;
// Natural-number field specs paired with emitted-definition theorems.
pub(super) fn neg_ref(x:u32)->u32{if x==0{0}else{2147483647-x}}
pub(super) fn cm_ref(x:u32)->(u32,u32){(x,0)}
pub(super) fn qm_ref(a:u32,b:u32)->(u32,u32,u32,u32){(a,b,0,0)}
#[kani::proof_for_contract(M31::neg)]
fn neg_contract(){let x=M31(kani::any());kani::assume(x.0<P);let _=x.neg();}
#[kani::proof_for_contract(CM31::from_m31)]
fn cm_contract(){let _=CM31::from_m31(M31(kani::any()));}
#[kani::proof_for_contract(QM31::from_cm31)]
fn qm_contract(){let _=QM31::from_cm31(CM31{a:M31(kani::any()),b:M31(kani::any())});}
'''
files={C+'field.rs':s,C+'NFQ_field.rs':code};inputs=json.loads((E/'NFQ_NATIVE_INPUTS.json').read_text());inputs.update(files);(E/'NFQ_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NFQ_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,s in files.items():patch+=difflib.unified_diff(base.splitlines(True) if n.endswith('/field.rs') else [],s.splitlines(True),fromfile='a/'+n if n.endswith('/field.rs') else '/dev/null',tofile='b/'+n)
(E/'NFQ_field.patch').write_text(''.join(patch))
