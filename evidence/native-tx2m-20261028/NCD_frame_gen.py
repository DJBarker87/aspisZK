from NCD_generate import *
t='''
#[cfg(kani)] mod NCD_fill_frame {
 use super::*;
 use alloc::boxed::Box;
'''
for count,label,ty in [(14759,'byte','u8'),(110,'word','u32')]:
 for claim in ['metadata','new_cell','exterior']:
  t+='#[kani::proof] #[kani::unwind(32)]\n'+attrs+'fn '+label+'_'+claim+'(){\n'
  t+=f'''let n:usize=kani::any();kani::assume(n<{count});let value:{ty}=kani::any();
 let backing:Box<[{ty};{count}]>=Box::new(kani::any());
 let ptr=Box::into_raw(backing) as *mut {ty};
 let mut out=unsafe{{Vec::from_raw_parts(ptr,n,{count})}};
 let j:usize=kani::any();kani::assume(j<{count});
 let old=unsafe{{*ptr.add(j)}};
 out.resize(n+1,value);
'''
  t+=dict(metadata=f'assert!(out.len()==n+1&&out.capacity()=={count}&&out.as_ptr()==ptr);',new_cell='assert!(out[n]==value);',exterior='if j!=n{assert!(unsafe{*ptr.add(j)}==old);}') [claim]+'\n}\n'
t+='}\n'
emit('crates/aspis-core/src/r0/heap.rs',t,'NCD_frame')
