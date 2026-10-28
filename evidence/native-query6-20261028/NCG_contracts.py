from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_native.rs').read_text()
# Result-return fidelity controls (same shape as decoder admission and allocator error return).
s+='''
#[kani::ensures(|r:&Result<u32,Error>| matches!(r,Ok(v) if *v==x))]
fn NCG_result_identity(x:u32)->Result<u32,Error>{Ok(x)}
#[kani::ensures(|r:&Result<u32,Error>| !matches!(r,Ok(v) if *v==x))]
fn NCG_result_inverted(x:u32)->Result<u32,Error>{Ok(x)}
#[kani::ensures(|_r:&Result<u32,Error>| true)]
fn NCG_result_weak(x:u32)->Result<u32,Error>{Ok(x)}
#[kani::modifies(a)]
#[kani::ensures(|_r:&Result<u32,Error>| true)]
fn NCG_result_modifies(a:&mut u32,b:&mut u32)->Result<u32,Error>{*a=1;*b=2;Ok(0)}
#[kani::proof_for_contract(NCG_result_identity)]
fn NCG_result_contract(){let x:u32=kani::any();let _=NCG_result_identity(x);}
#[kani::proof_for_contract(NCG_result_inverted)]
fn NCG_result_wrong(){let x:u32=kani::any();let _=NCG_result_inverted(x);}
#[kani::proof_for_contract(NCG_result_weak)]
fn NCG_result_weak_contract(){let x:u32=kani::any();let _=NCG_result_weak(x);}
#[kani::proof]
fn NCG_result_real(){let x:u32=kani::any();assert_eq!(NCG_result_weak(x),Ok(x));}
#[kani::proof]
#[kani::stub_verified(NCG_result_weak)]
fn NCG_result_unimplied(){let x:u32=kani::any();assert_eq!(NCG_result_weak(x),Ok(x));}
#[kani::proof_for_contract(NCG_result_modifies)]
fn NCG_result_frame_wrong(){let mut a:u32=kani::any();let mut b:u32=kani::any();let _=NCG_result_modifies(&mut a,&mut b);}
#[kani::proof]
#[kani::stub_verified(NCG_result_identity)]
fn NCG_result_install(){let x:u32=kani::any();assert_eq!(NCG_result_identity(x),Ok(x));}
#[kani::proof]
#[kani::stub_verified(NCG_result_identity)]
fn NCG_result_install_negative(){let x:u32=kani::any();assert_ne!(NCG_result_identity(x),Ok(x));}
'''
Path('/tmp/NCG_contracts.rs').write_text(s)
# Pending sync only after active source is terminal.
(E/'NCG_contracts.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
