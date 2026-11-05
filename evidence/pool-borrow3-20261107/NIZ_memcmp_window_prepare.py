import sys
sys.dont_write_bytecode=True
from NIZ_native_prepare import stage,attrs
mode=sys.argv[1]
body='let mut bytes=[kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()];let left=usize::from(kani::any::<u8>());let right=usize::from(kani::any::<u8>());let observer=usize::from(kani::any::<u8>());kani::assume(left<3&&right<3&&observer<3);let a=bytes[left];let b=bytes[right];let frame=bytes[observer];let reply=unsafe{memcmp(bytes.as_ptr().add(left).cast(),bytes.as_ptr().add(right).cast(),1)};'
if mode=='frame-negative':body+='bytes[observer]=frame^1;'
body+='assert!((reply==0)'+('!=' if mode=='negative' else '==')+'(a==b));assert!(bytes[observer]==frame);'
source='use core::ffi::{c_void,c_int};unsafe extern "C"{fn memcmp(a:*const c_void,b:*const c_void,n:usize)->c_int;}\n'+attrs()+'\n#[kani::proof]\nfn certificate(){'+body+'}\n'
stage('programs/aspis-pool/src/processor.rs',source,'actual memcmp byte iteration on arbitrary aliased window and observed frame',mode,'All bytes arbitrary; arbitrary left/right/observer positions in the local three-byte carrier; same or different pointers, no initialized-count restriction.','Generic iteration/host-loop association, arbitrary-span framing and original key-field/caller association remain separately required.',dict(expected_verdict='PASS' if mode=='positive' else 'FAIL',member='host_memcmp_window',native_args=['--unwind','4']))
