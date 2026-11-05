from pathlib import Path
import sys
sys.dont_write_bytecode=True
from NIZ_native_prepare import stage,attrs
negative=sys.argv[1]=='negative'
source='use core::ffi::{c_void,c_int}; unsafe extern "C" {fn memcmp(a:*const c_void,b:*const c_void,n:usize)->c_int;}\n'+attrs()+'\n#[kani::proof]\nfn certificate(){let a:u8=kani::any();let b:u8=kani::any();let before_a=a;let before_b=b;let reply=unsafe{memcmp((&a as *const u8).cast(),(&b as *const u8).cast(),1)};assert!((reply==0)'+('!=' if negative else '==')+'(a==b));assert!(a==before_a);assert!(b==before_b);}\n'
stage('programs/aspis-pool/src/processor.rs',source,'one actual host memcmp byte iteration',sys.argv[1],'Two arbitrary valid readable single-byte locations, arbitrary alias-free caller byte values; no allocation or SDK carrier.','Host builtin step must be associated with the retained key-comparison GOTO loop; source/runtime/ELF associations remain separately scoped.',dict(expected_verdict='FAIL' if negative else 'PASS',member='host_memcmp_step',native_args=['--unwind','2']))
