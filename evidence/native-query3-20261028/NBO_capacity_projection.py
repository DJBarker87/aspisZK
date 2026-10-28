from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NBO_native.rs.txt').read_text()
s+='''
fn NBO_project_capacity<T:Copy,const N:usize>(initial:[T;N],cap:usize) {
 kani::assume(cap>=N);kani::assume(cap<=isize::MAX as usize/core::mem::size_of::<T>());
 let mut v:Vec<T>=Vec::with_capacity(cap);v.extend_from_slice(&initial);
 let ptr=v.as_ptr();assert_eq!(v.len(),N);assert_eq!(v.capacity(),cap);
 {let s:&[T]=&v;assert_eq!(s.len(),N);assert_eq!(s.as_ptr(),ptr);}
 {let s:&mut[T]=&mut v;assert_eq!(s.len(),N);assert_eq!(s.as_ptr(),ptr);}
 assert_eq!(v.len(),N);assert_eq!(v.capacity(),cap);assert_eq!(v.as_ptr(),ptr);
 kani::cover!(cap==N);kani::cover!(cap>N);
}
'''
raw=','.join('kani::any::<[u64;4]>()' for _ in range(64))
q=lambda:'K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}'
items=[('raw','['+raw+']'),('weight','['+','.join(q() for _ in range(64))+']'),('line','['+','.join('M31(kani::any())' for _ in range(10))+']'),('inverse','['+','.join('['+','.join('M31(kani::any())' for _ in range(5))+']' for _ in range(10))+']')]
for name,values in items:
 s+='#[kani::proof]\n#[kani::unwind(4096)]\nfn NBO_capacity_'+name+'_projection(){NBO_project_capacity('+values+',kani::any());}\n'
(E/'NBO_native.rs.txt').write_text(s)
