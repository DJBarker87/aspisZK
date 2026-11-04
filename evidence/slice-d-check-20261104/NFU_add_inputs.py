"""Own sidecar edits only; emits a retained patch and updates source pins."""
from pathlib import Path
import json,hashlib,difflib,sys
E=Path(__file__).resolve().parent

def update(files,label):
 p=E/'NFU_NATIVE_INPUTS.json';old=json.loads(p.read_text());patch=[]
 for n,t in files.items():
  before=old.get(n,'')
  patch+=difflib.unified_diff(before.splitlines(True),t.splitlines(True),fromfile='a/'+n if n in old else '/dev/null',tofile='b/'+n)
 old.update(files);p.write_text(json.dumps(old,indent=1)+'\n')
 pins=json.loads((E/'NFU_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFU_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');(E/(label+'.patch')).write_text(''.join(patch))
if __name__=='__main__':
 p='crates/aspis-r1-cost-probe/src/NFU_wire.rs';s=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text())[p]
 s+='''
#[kani::ensures(|r| *r<=2)] #[kani::modifies()]
fn weak_u8()->u8{1}
#[kani::proof_for_contract(weak_u8)]
fn u8_real(){assert_eq!(weak_u8(),1);}
#[kani::proof] #[kani::stub_verified(weak_u8)]
fn u8_unimplied(){assert_eq!(weak_u8(),1);}
#[kani::ensures(|r| *r==1)] #[kani::modifies(&mut x[0])]
fn bad_u8_frame(x:&mut[u8;2])->u8{x[1]=x[1].wrapping_add(1);1}
#[kani::proof_for_contract(bad_u8_frame)]
fn u8_frame(){let mut x:[u8;2]=kani::any();let _=bad_u8_frame(&mut x);}
'''
 update({p:s},'NFU_u8_fidelity')
