"""Prefix-owned frozen-body annotations. All changes stay in the external copy."""
from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];Q=E.parent/'slice-d-define-20261104';C='crates/aspis-core/src/'
inputs={};patch=[]
# Retain byte-pinned predecessor scratch dependencies, without relying on their harnesses.
pins=json.loads((Q/'NFQ_SOURCE_PINS.json').read_text())
def frozen(n):return subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],cwd=R,text=True)
def put(n,s):
 inputs[n]=s;pins[n]=hashlib.sha256(s.encode()).hexdigest()
 old=frozen(n) if not Path(n).name.startswith('NFT_') else ''
 patch.extend(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
s=frozen(C+'field.rs')
# The exact body is unmodified; contracts describe complete fixed-size output.
for sig,width,fun in [('pub fn write_le_bytes(self, out: &mut [u8])',8,'cm_bytes'),('pub fn write_le_bytes(self, out: &mut [u8])',16,'qm_bytes')]:
 # Disambiguate by declaration order.
 pos=s.index(sig) if width==8 else s.rindex(sig)
 req=f'#[cfg_attr(kani,kani::requires(out.len()=={width}))]\n#[cfg_attr(kani,kani::modifies(out))]\n'
 ens=f'#[cfg_attr(kani,kani::ensures(|_| NFT_field::{fun}_matches(self,out) != cfg!(NFT_invert)))]\n'
 s=s[:pos]+req+ens+s[pos:]
s+='\n#[cfg(kani)]\n#[path="NFT_field.rs"]\nmod NFT_field;\n'
put(C+'field.rs',s)
put(C+'NFT_field.rs','''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
pub(super) fn cm_bytes_matches(v:CM31,b:&[u8])->bool{
 b[0]==v.a.0 as u8 && b[1]==(v.a.0>>8)as u8 && b[2]==(v.a.0>>16)as u8 && b[3]==(v.a.0>>24)as u8 &&
 b[4]==v.b.0 as u8 && b[5]==(v.b.0>>8)as u8 && b[6]==(v.b.0>>16)as u8 && b[7]==(v.b.0>>24)as u8
}
pub(super) fn qm_bytes_matches(v:QM31,b:&[u8])->bool{cm_bytes_matches(v.c0,&b[0..8]) && cm_bytes_matches(v.c1,&b[8..16])}
#[kani::proof_for_contract(CM31::write_le_bytes)]
KMXL
fn cm_write(){let v=any_cm();let mut b:[u8;8]=kani::any();v.write_le_bytes(&mut b);}
#[kani::proof_for_contract(QM31::write_le_bytes)]
KMXL
fn qm_write(){let v=any_q();let mut b:[u8;16]=kani::any();v.write_le_bytes(&mut b);}
#[kani::proof]
KMXL
fn copy8_positive(){let a:[u8;8]=kani::any();let mut b:[u8;8]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<8);assert!(b[i]==a[i]);}
#[kani::proof]
KMXL
fn copy8_negative(){let a:[u8;8]=kani::any();let mut b:[u8;8]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<8);assert!(b[i]!=a[i]);}
#[kani::proof]
KMXL
fn copy16_positive(){let a:[u8;16]=kani::any();let mut b:[u8;16]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<16);assert!(b[i]==a[i]);}
#[kani::proof]
KMXL
fn copy16_negative(){let a:[u8;16]=kani::any();let mut b:[u8;16]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<16);assert!(b[i]!=a[i]);}
'''.replace('KMXL','''#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]'''))
# Keep the predecessor allocator feature for exact KMX stubs, but erase its harness modules.
s=frozen(C+'lib.rs').replace('#![no_std]','#![cfg_attr(kani,feature(allocator_api))]\n#![no_std]',1);put(C+'lib.rs',s)
(E/'NFT_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n');(E/'NFT_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');(E/'NFT_native.patch').write_text(''.join(patch))
