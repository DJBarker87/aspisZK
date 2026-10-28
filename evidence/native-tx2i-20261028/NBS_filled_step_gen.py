from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent;p='crates/aspis-core/src/r0/heap.rs';s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
s+=''.join(l[1:] for l in (E/'NBS_filled.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
t=r'''
#[cfg(kani)] mod NBS_buffer {
 use super::*;
 #[kani::proof] #[kani::unwind(16)]
 fn resize_one(){
  let old:[u32;4]=kani::any();let mut v:Vec<u32>=old.into();let m:usize=kani::any();kani::assume(m<4);
  v.truncate(m);let ptr=v.as_ptr();let value:u32=kani::any();v.resize(m+1,value);
  assert!(v.len()==m+1&&v.as_ptr()==ptr);let j:usize=kani::any();kani::assume(j<=m);assert!(v[j]==if j==m{value}else{old[j]});
 }
 static mut EXPECT:usize=0;static mut CALLS:u8=0;
 fn denied(v:&mut Vec<u32>,n:usize)->Result<(),alloc::collections::TryReserveError>{
  unsafe{assert!(n==EXPECT);assert!(CALLS==0);CALLS=1;}
  assert!(v.len()==0&&v.capacity()==0);
  let mut error=Vec::<u32>::new();Err(error.try_reserve(usize::MAX).unwrap_err())
 }
 fn forbidden_resize(_: &mut Vec<u32>,_:usize,_:u32){assert!(false);}
 #[kani::proof] #[kani::unwind(4)]
 #[kani::stub(Vec::<u32>::try_reserve_exact,denied)] #[kani::stub(Vec::<u32>::resize,forbidden_resize)]
 fn reserve_denied(){
  let n:usize=kani::any();let value:u32=kani::any();unsafe{EXPECT=n;CALLS=0;}
  assert!(matches!(filled(n,value),Err(super::Error::Allocation)));unsafe{assert!(CALLS==1);}
 }
}
'''
(E/'NBS_buffer.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+t).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
