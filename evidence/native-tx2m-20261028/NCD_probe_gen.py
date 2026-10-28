from NCD_generate import *
t='''
#[cfg(kani)] mod NCD_prestate {
use super::*;
#[kani::proof] #[kani::unwind(512)]
'''+attrs+'''fn word_constructor(){
 let n:usize=kani::any();kani::assume(n<=110);
 let backing=alloc::boxed::Box::new(kani::any::<[u32;110]>());
 let ptr=alloc::boxed::Box::into_raw(backing) as *mut u32;
 let out=unsafe{Vec::from_raw_parts(ptr,n,110)};
 assert!(out.len()==n&&out.capacity()==110&&out.as_ptr()==ptr);
}
}
'''
emit('crates/aspis-core/src/r0/heap.rs',t,'NCD_probe')
