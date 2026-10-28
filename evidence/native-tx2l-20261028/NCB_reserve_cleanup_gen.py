from NCB_generate import *
p='crates/aspis-core/src/r0/heap.rs'
t='\n#[cfg(kani)] mod NCB_allocation {\nuse super::*;\n'
for ty,bound,name in [('u8',14759,'byte'),('u32',110,'word')]:
 t+='#[kani::proof] #[kani::unwind(32)]\n'+attrs+f'fn reserve_{name}()'+'{\n'
 t+=f'''let n:usize=kani::any();kani::assume(n>0&&n<={bound});let mut out=Vec::<{ty}>::new();
 let result=out.try_reserve_exact(n);match result{{Ok(())=>{{assert!(out.len()==0&&out.capacity()>=n);assert!(!out.as_ptr().is_null());kani::cover!(true);}},Err(_)=>{{assert!(out.len()==0&&out.capacity()==0);}}}}
'''+'}\n'
t+='#[kani::proof] #[kani::unwind(8)]\n'+attrs+'''fn zst_bounded(){let n:usize=kani::any();kani::assume(n>0&&n<=3);let out=filled(n,()).unwrap();assert!(out.len()==n&&out.capacity()==usize::MAX);let i:usize=kani::any();kani::assume(i<n);assert!(out.get(i)==Some(&()));}\n'''
t+='''static mut EXPECT:*mut u8=core::ptr::null_mut();static mut SIZE:usize=0;static mut ALIGN:usize=0;static mut CALLS:u8=0;
 fn free(ptr:*mut u8,layout:alloc::alloc::Layout){unsafe{assert!(CALLS==0);CALLS=1;assert!(ptr==EXPECT);assert!(layout.size()==SIZE&&layout.align()==ALIGN);}}
'''
for ty in ['u8','u32']:
 for n in [1,2]:
  t+='#[kani::proof] #[kani::unwind(64)]\n'+attrs+'#[kani::stub(alloc::alloc::dealloc,free)]\n'+f'fn cleanup_{ty}_{n}()'+'{\n'
  t+=f'''let value:{ty}=kani::any();let out=filled({n},value).unwrap();assert!(out.len()=={n});let j:usize=kani::any();kani::assume(j<{n});assert!(out[j]==value);
 unsafe{{EXPECT=out.as_ptr() as *mut u8;SIZE=out.capacity()*core::mem::size_of::<{ty}>();ALIGN=core::mem::align_of::<{ty}>();CALLS=0;}}
 drop(out);unsafe{{assert!(CALLS==1);}}
'''+'}\n'
t+='#[kani::proof] #[kani::unwind(32)]\n'+attrs+'#[kani::stub(alloc::alloc::dealloc,free)]\n'+'''fn copy_negative(){let a=[0u32,0,0,0,0,0,0,1,0,0,0,0,0,0,0,512];let mut b=[0u32;16];b.copy_from_slice(&a);assert!(b[15]==0);}
}\n'''
emit(p,t,'NCB_reserve_cleanup')
