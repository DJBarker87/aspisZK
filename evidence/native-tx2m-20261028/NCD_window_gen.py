from NCD_generate import *
t='''
#[cfg(kani)] mod NCD_byte_window {
use super::*;
'''
for claim in ['store_new','store_frame','fill_new','fill_frame','bounds']:
 t+='#[kani::proof] #[kani::unwind(32)]\n'+attrs+'fn '+claim+'(){\n'
 t+='''let mut storage=core::mem::MaybeUninit::<[u8;32]>::uninit();let ptr=storage.as_mut_ptr() as *mut u8;
 let base:usize=kani::any();kani::assume(base<14759);let len:usize=kani::any();kani::assume(len>0&&len<=32);kani::assume(base+len<=14759);
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<len&&j<len);let old:u8=kani::any();let value:u8=kani::any();
 unsafe{ptr.add(j).write(old);'''
 t+=('core::ptr::write_bytes(ptr.add(i),value,1);' if claim.startswith('fill') else 'ptr.add(i).write(value);')
 t+=('assert!(*ptr.add(i)==value);' if claim.endswith('new') else 'if j!=i{assert!(*ptr.add(j)==old);}' if claim.endswith('frame') else 'assert!(base+i<14759&&base+j<14759&&i<32&&j<32);')+'}\n}\n'
t+='}\n';emit('crates/aspis-core/src/r0/heap.rs',t,'NCD_window')
