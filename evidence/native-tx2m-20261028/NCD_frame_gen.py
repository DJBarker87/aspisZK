from NCD_generate import *
t='''
#[cfg(kani)] mod NCD_fill_frame {
 use super::*;
 use alloc::boxed::Box;
'''
for count,label,ty in [(14759,'byte','u8'),(110,'word','u32')]:
 t+='#[kani::proof] #[kani::unwind(32)]\n'+attrs+'fn '+label+'_reserve_exact(){\n'
 t+=f'''let n:usize=kani::any();kani::assume(n<={count});let mut out=Vec::<{ty}>::new();
 let result=out.try_reserve_exact(n);match result{{Ok(())=>{{assert!(out.len()==0&&out.capacity()==n);kani::cover!(true);}},Err(_)=>{{assert!(out.len()==0&&out.capacity()==0);}}}}\n}}\n'''
for count,label,ty in [(110,'word','u32')]:
 for claim in ['metadata','new_cell','exterior']:
  t+='#[kani::proof] #[kani::unwind(512)]\n'+attrs+'fn '+label+'_'+claim+'(){\n'
  t+=f'''let n:usize=kani::any();kani::assume(n<{count});let value:{ty}=kani::any();
 let backing:Box<[{ty};{count}]>=Box::new(kani::any());
 let ptr=Box::into_raw(backing) as *mut {ty};
 let mut out=unsafe{{Vec::from_raw_parts(ptr,n,{count})}};
 let j:usize=kani::any();kani::assume(j<{count});
 let old=unsafe{{*ptr.add(j)}};
 out.resize(n+1,value);
'''
  t+=dict(metadata=f'assert!(out.len()==n+1&&out.capacity()=={count}&&out.as_ptr()==ptr);',new_cell='assert!(out[n]==value);',exterior='if j!=n{assert!(unsafe{*ptr.add(j)}==old);}') [claim]+'\n}\n'
for claim in ['store_cell','store_frame','fill_cell','fill_frame']:
 t+='#[kani::proof] #[kani::unwind(32)]\n'+attrs+'fn byte_'+claim+'(){\n'
 t+='''let mut storage=core::mem::MaybeUninit::<[u8;14759]>::uninit();let ptr=storage.as_mut_ptr() as *mut u8;
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<14759&&j<14759);let old:u8=kani::any();let value:u8=kani::any();
 unsafe{ptr.add(j).write(old);'''
 t+=('core::ptr::write_bytes(ptr.add(i),value,1);' if claim.startswith('fill') else 'ptr.add(i).write(value);')
 t+=('assert!(*ptr.add(i)==value);' if claim.endswith('cell') else 'if j!=i{assert!(*ptr.add(j)==old);}')+'}\n}\n'
t+='}\n'
emit('crates/aspis-core/src/r0/heap.rs',t,'NCD_frame')
