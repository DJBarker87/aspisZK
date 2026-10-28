from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
get=lambda n:subprocess.check_output(['git','show',F+':'+n]).decode()
files={}
n='crates/aspis-r1-cost-probe/src/multiproof.rs';s=get(n)
for sig,req,post in [
('fn index_at(indices: &[u32; MAX_BATCH], index: usize) -> u32 {','index < MAX_BATCH','*r == NDD_multiproof::reference::index_ref(indices,index)'),
('fn value_at(values: &[[u8; 32]; MAX_BATCH], index: usize) -> [u8; 32] {','index < MAX_BATCH','*r == NDD_multiproof::reference::value_ref(values,index)'),
('fn root_matches(values: &[[u8; 32]; MAX_BATCH], root: &[u8; 32]) -> bool {','true','*r == NDD_multiproof::reference::root_ref(values,root)'),
]:
 assert s.count(sig)==1
 s=s.replace(sig,f'#[cfg_attr(kani, kani::requires({req}))]\n#[cfg_attr(kani, kani::ensures(|r| NDD_multiproof::verdict({post})))]\n'+sig)
sig='pub const fn bits(self) -> u32 {'
s=s.replace(sig,'#[cfg_attr(all(kani,NDD_bits),kani::ensures(|r| NDD_multiproof::verdict(*r == NDD_multiproof::reference::bits_ref(matches!(self,Self::Eight)))))]\n    '+sig)
files[n]=s+'\n#[cfg(kani)]\n#[path="NDD_multiproof.rs"]\nmod NDD_multiproof;\n'
files['crates/aspis-r1-cost-probe/src/NDD_multiproof.rs']='''use super::*;
#[path="NDD_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn verdict(v:bool)->bool{if cfg!(NDD_negative_verifier){!v}else{v}}
#[kani::proof_for_contract(index_at)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn index_contract(){let x:[u32;16]=kani::any();index_at(&x,kani::any());}
#[kani::proof_for_contract(value_at)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn value_contract(){let x:[[u8;32];16]=kani::any();value_at(&x,kani::any());}
#[kani::proof_for_contract(root_matches)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn root_contract(){let x:[[u8;32];16]=kani::any();let r:[u8;32]=kani::any();root_matches(&x,&r);}
#[cfg(NDD_bits)] #[kani::proof_for_contract(Arity::bits)]
fn bits_contract(){let x=if kani::any(){Arity::Eight}else{Arity::Two};x.bits();}
'''
files['crates/aspis-r1-cost-probe/src/NDD_multiproof.rs'] += (E/'NDD_digest.rs').read_text()+(E/'NDD_wellformed.rs').read_text()
n='crates/aspis-r1-cost-probe/src/weights.rs';s=get(n);sig='fn shared_two_point_guard(w:&Weights,folds:usize)->bool {'
post='*r == NDD_weights::reference::guard_ref(w.variant==Variant::S2,folds,w.factors[0][2]==w.factors[2][2],w.factors[0][3]==w.factors[2][3])'
s=s.replace(sig,'#[cfg_attr(kani,kani::ensures(|r| NDD_weights::verdict('+post+')))]\n'+sig)
files[n]=s+'\n#[cfg(kani)]\n#[path="NDD_weights.rs"]\nmod NDD_weights;\n'
files['crates/aspis-r1-cost-probe/src/NDD_weights.rs']='''use super::*;
#[path="NDD_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn verdict(v:bool)->bool{if cfg!(NDD_negative_guard){!v}else{v}}
fn q()->K{let x:[u32;4]=kani::any();K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
#[kani::proof_for_contract(shared_two_point_guard)] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn guard_contract(){let w=Weights{variant:match kani::any::<u8>()%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D},
factors:core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|q()))),
points:core::array::from_fn(|_|core::array::from_fn(|_|q())),extra:core::array::from_fn(|_|q())};
shared_two_point_guard(&w,kani::any());}
'''
files['crates/aspis-r1-cost-probe/src/NDD_weights.rs'] += (E/'NDD_selector.rs').read_text()
n='crates/aspis-r1-cost-probe/src/lib.rs';files[n]='#![cfg_attr(kani,feature(allocator_api))]\n'+get(n)+'\n#[cfg(kani)]\nmod NDD_controls;\n'
files['crates/aspis-r1-cost-probe/src/NDD_controls.rs']=(E/'NDD_controls.rs').read_text()
files['crates/aspis-r1-cost-probe/src/NDD_reference.rs']=(E/'NDD_reference.rs').read_text()
patch=''
for n,v in files.items():
 old=get(n) if not Path(n).name.startswith('NDD_') else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),v.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NDD_EXTRA.patch').write_text(patch)
code='''from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-native-front1-20261028');s=b/'NDD_src'
for n,v in json.loads(PAYLOAD).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.is_symlink():p.unlink()
 p.write_text(v)
pins={str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}
(b/'NDD_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
'''.replace('PAYLOAD',repr(json.dumps(files)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
print('installed extra scratch contracts')
