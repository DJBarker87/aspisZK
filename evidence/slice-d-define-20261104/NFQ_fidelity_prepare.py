from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-r1-cost-probe/src/'
code='''// Rule (t) fidelity controls. State is exclusively local.
#[kani::ensures(|r| *r <= 2)]
#[kani::modifies()]
fn weak_usize()->usize{1}
#[kani::proof_for_contract(weak_usize)]
fn usize_real(){assert_eq!(weak_usize(),1);}
#[kani::proof] #[kani::stub_verified(weak_usize)]
fn usize_unimplied(){assert_eq!(weak_usize(),1);}
#[kani::modifies(&mut x[0])]
#[kani::ensures(|r| *r==1)]
fn usize_badframe(x:&mut [u8;2])->usize{x[1]=x[1].wrapping_add(1);1}
#[kani::proof_for_contract(usize_badframe)]
fn usize_frame(){let mut x:[u8;2]=kani::any();let _=usize_badframe(&mut x);}
#[kani::ensures(|r| r.is_some())]
#[kani::modifies()]
fn weak_option()->Option<(u8,usize)>{Some((7,37))}
#[kani::proof_for_contract(weak_option)]
fn option_real(){assert_eq!(weak_option(),Some((7,37)));}
#[kani::proof] #[kani::stub_verified(weak_option)]
fn option_unimplied(){assert_eq!(weak_option(),Some((7,37)));}
#[kani::modifies(&mut x[0])]
#[kani::ensures(|r| r.is_some())]
fn option_badframe(x:&mut [u8;2])->Option<(u8,usize)>{x[1]=x[1].wrapping_add(1);Some((7,37))}
#[kani::proof_for_contract(option_badframe)]
fn option_frame(){let mut x:[u8;2]=kani::any();let _=option_badframe(&mut x);}
'''
base=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+C+'lib.rs'],text=True,cwd=R)
lib=base+'\n#[cfg(kani)]\n#[path="NFQ_fidelity.rs"]\nmod NFQ_fidelity;\n'
files={C+'lib.rs':lib,C+'NFQ_fidelity.rs':code}
(E/'NFQ_NATIVE_INPUTS.json').write_text(json.dumps(files,indent=1)+'\n')
pins=json.loads((E/'NFQ_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=''.join(difflib.unified_diff(base.splitlines(True),lib.splitlines(True),fromfile='a/'+C+'lib.rs',tofile='b/'+C+'lib.rs'))+''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+C+'NFQ_fidelity.rs'))
(E/'NFQ_fidelity.patch').write_text(patch)
