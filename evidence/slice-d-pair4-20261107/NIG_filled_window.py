from pathlib import Path
import subprocess,difflib,sys
E=Path(__file__).resolve().parent
base,kbase=map(int,sys.argv[1:]);assert base in range(0,64,4)and kbase in [0,32]and base+3>=kbase
h='''extern crate alloc;
use crate::field::{QM31 as Q,CM31 as C,M31 as M};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn q(x:[u32;4])->Q{Q{c0:C{a:M(x[0]),b:M(x[1])},c1:C{a:M(x[2]),b:M(x[3])}}}
fn words(x:Q)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
#[kani::proof]#[kani::unwind(6)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_frame(){
 match kani::any::<u8>()&3 {0=>step::<BASE>(),1=>step::<NEXT1>(),2=>step::<NEXT2>(),_=>step::<NEXT3>()}
}
fn step<const P:usize>(){
 let p:usize=P;
 let k:usize=KBASE+usize::from(kani::any::<u8>()&31);kani::assume(k<=p);
 let limb:usize=kani::any();kani::assume(limb<4);
 let mut out=Vec::<Q>::new();
 if out.try_reserve_exact(64).is_err(){assert!(out.is_empty());return;}
 let ptr=out.as_mut_ptr();let cap=out.capacity();
 // Harness prestate: exactly the initialized zero prefix, arbitrary new cell,
 // and UNINITIALIZED remaining spare storage. No spare-zero precondition.
 unsafe{core::ptr::write_bytes(ptr,0,p);ptr.add(p).write(q(kani::any()));out.set_len(p);}
 out.resize(p+1,Q::ZERO);
 if cfg!(NIG_corrupt){out[k]=q([1;4]);}
 assert!(words(out[k])[limb]==0);
 assert!(out.as_ptr()==ptr&&out.len()==p+1&&out.capacity()==cap);
}
'''.replace('KBASE',str(kbase)).replace('NEXT1',str(base+1)).replace('NEXT2',str(base+2)).replace('NEXT3',str(base+3)).replace('BASE',str(base))
core=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-core/src/lib.rs'],text=True);new=core.replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')+'\n#[cfg(kani)] #[path="NIG_filled.rs"] mod NIG_filled;\n'
p=''.join(difflib.unified_diff(core.splitlines(True),new.splitlines(True),fromfile='a/crates/aspis-core/src/lib.rs',tofile='b/crates/aspis-core/src/lib.rs'))
p+='--- /dev/null\n+++ b/crates/aspis-core/src/NIG_filled.rs\n@@ -0,0 +1,'+str(len(h.splitlines()))+' @@\n'+''.join('+'+l for l in h.splitlines(True))
(E/'NIG_filled.patch').write_text(p)
