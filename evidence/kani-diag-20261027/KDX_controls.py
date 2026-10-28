from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KDX_host as h
s=(E/'KDX_copy.rs.txt').read_text()
s+='''
// Negative control: this assertion is FALSE in native Rust on the retained fixture.
#[kani::proof] #[kani::unwind(17)]
fn KDX_false_zero(){let mut input=[0u32;16];input[7]=1;input[15]=512;let mut level=[0u32;16];let n:usize=kani::any();kani::assume(n==16);level[..n].copy_from_slice(&input[..n]);assert!(level[15]==0);}
// Constant whole-array slice control; same element width and source domain.
#[kani::proof] #[kani::unwind(17)]
fn KDX_constant_copy(){let input:[u32;16]=kani::any();let mut level=[0u32;16];level.copy_from_slice(&input);let k:usize=kani::any();kani::assume(k<16);assert_eq!(level[k],input[k]);}
'''
(E/'KDX_copy.rs.txt').write_text(s)
h.admit('KDX_CONTROLUPLOAD')
r=h.remote_py(f'from pathlib import Path\nPath({(h.B+"/KDX_src/crates/aspis-r1-cost-probe/src/KDX_copy.rs")!r}).write_text({s!r})');assert r.returncode==0,r.stderr
