from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
read=lambda p:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
x={n:read(n) for n in ['Cargo.toml','Cargo.lock','crates/aspis-r1-cost-probe/src/lib.rs']}
patch=(R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
for part in patch.split('diff --git ')[1:]:
 n=part.splitlines()[0].split(' b/')[1];x[n]='\n'.join(l[1:] for l in part.splitlines() if l.startswith('+') and not l.startswith('+++'))+'\n'
x['crates/aspis-r1-cost-probe/src/lib.rs']='#![cfg_attr(kani,feature(allocator_api))]\n'+x['crates/aspis-r1-cost-probe/src/lib.rs']
x['crates/aspis-r1-cost-probe/src/lib.rs']+='\n#[cfg(kani)]\n#[path="NHH_fields.rs"]\nmod NHH_fields;\n'
s='''#![allow(non_snake_case)]
use aspis_core::field::{M31,CM31,QM31,WideExact,P};
use aspis_core::r0::scalar::CodeField;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn q(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn cm(x:CM31)->[u32;2]{[x.a.0,x.b.0]}
fn w(x:WideExact)->[u32;8]{let a=q(x.c0());let b=q(x.c1());[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]]}
fn check(actual:bool){if cfg!(NHH_invert){assert!(!actual)}else{assert!(actual)}}
'''
for name,typ,proj,expected in [('m31','M31','out.0','x%P'),('cm31','CM31','cm(out)','[x%P,0]'),('qm31','QM31','q(out)','[x%P,0,0,0]'),('wide','WideExact','w(out)','[x%P,0,0,0,0,0,0,0]')]:
 s+=f'''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn {name}_embed(){{let x:u32=kani::any();let out=<{typ} as CodeField>::from_m31(M31(x));check({proj}=={expected});}}
'''
s+='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn cm_inherent(){let x:u32=kani::any();let out=CM31::from_m31(M31(x));check(cm(out)==[x,0]);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn qm_neg(){let a:[u32;4]=kani::any();kani::assume(a[0]<P&&a[1]<P&&a[2]<P&&a[3]<P);let x=QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}};let out=x.neg();let n=|v:u32|if v==0{0}else{P-v};check(q(out)==[n(a[0]),n(a[1]),n(a[2]),n(a[3])]);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn copy_control(){let src:[u8;32]=kani::any();let mut dst=[0u8;32];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),32)};check(dst==src);}
'''
(E/'NHH_fields.rs.txt').write_text(s);x['crates/aspis-r1-cost-probe/src/NHH_fields.rs']=s
(E/'NHH_NATIVE_INPUTS.json').write_text(json.dumps(x))
(E/'NHH_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()},indent=2)+'\n')
(E/'NHH_KMX_PIN.json').write_text(json.dumps({'patch':'evidence/kani-mitig-20261028/KMX_copy_stubs.patch','sha256':hashlib.sha256(patch.encode()).hexdigest(),'source_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'},indent=2)+'\n')
