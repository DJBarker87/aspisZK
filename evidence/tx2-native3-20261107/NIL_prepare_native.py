from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(n):return subprocess.check_output(['git','show',REV+':'+n],text=True)
lib='crates/aspis-r1-cost-probe/src/lib.rs';vr='crates/aspis-r1-cost-probe/src/verifier.rs'
inputs={lib:frozen(lib).replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')+'\n#[cfg(kani)] include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n',vr:frozen(vr)+'\n#[cfg(kani)]\n#[path="NIL_reader_native.rs"]\nmod NIL_reader_native;\n'}
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn limb(x:E,j:usize)->u32{let q=if j<4{x.c0()}else{x.c1()};match j&3{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
fn value<const O:usize>(){let bytes:[u8;1768]=kani::any();let mut r=Reader{bytes:&bytes,at:O};let j:usize=kani::any();kani::assume(j<8);let out=r.e();if let Ok(value)=out{let b=O+4*j;let expected=u32::from_le_bytes([bytes[b],bytes[b+1],bytes[b+2],bytes[b+3]]);let actual=limb(value,j);assert_eq!(actual,if cfg!(NIL_invert){expected^1}else{expected});}}
'''
families=[]
for i,o in enumerate([176,208,240,272,632,664]):
 for renamed in [False,True]:
  n='e_value'+str(i)+('_renamed' if renamed else '')
  s+='#[kani::proof]\n#[kani::unwind(36)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn '+n+'(){value::<'+str(o)+'>();}\n'
 families.append({'family':'e_value'+str(i),'offset':o,'function':'verifier::NIL_reader_native::e_value'+str(i),'rename':'verifier::NIL_reader_native::e_value'+str(i)+'_renamed','status':'planned','domain':'SAME checkpoint1768; actual resume E offset; arbitrary bytes; full success value, each selected limb<8; no canonical input assumed'})
for name in json.loads(Path('evidence/tx2-native2-20261107/NID_NATIVE_INPUTS.json').read_text()):
 if name.startswith('tools/'):
  inputs[name]=frozen(name)
inputs['crates/aspis-r1-cost-probe/src/NIL_reader_native.rs']=s
(E/'NIL_reader_native.rs.txt').write_text(s)
(E/'NIL_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=2)+'\n')
m=json.loads(Path('evidence/extract-stage-20261106/NHR_STAGING_MANIFEST.json').read_text())
pins={n:r['sha256'] for n,r in m['files'].items()}
for n,s in inputs.items():pins[n]=hashlib.sha256(s.encode()).hexdigest()
(E/'NIL_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(E/'NIL_NATIVE_MATRIX.json').write_text(json.dumps(families,indent=2)+'\n')
(E/'NIL_gate.py').write_text(Path('evidence/tx2-native2-20261107/NID_gate.py').read_text().replace('NID','NIL'))
# Commit the reviewable patch, scratch source only.
import difflib
patch=''
for n,s in inputs.items():
 old=frozen(n) if not n.endswith('NIL_reader_native.rs') else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NIL_native.patch').write_text(patch)
