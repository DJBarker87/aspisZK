from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
basis=','.join('M31(kani::any())' for _ in range(256))
s+='''
// ONE literal basis iteration on an arbitrary pre-state, including all other
//255 arbitrary cells. Copy bound covers the entire1024-byte basis backing.
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBO_m31_canonical_reply)]
fn NBO_basis_store_full_copy_bound(){
 let mut basis:[M31;256]=['''+basis+'''];let n:usize=kani::any();kani::assume(n>=1&&n<=128);
 let j:usize=kani::any();kani::assume(j<n);let i:usize=kani::any();kani::assume(i<256);
 let node:u32=kani::any();kani::assume(node<2147483647);kani::assume(basis[j].0<2147483647);
 let old=basis[i];let input=basis[j];
 basis[n+j]=basis[j].mul(M31(node));
 unsafe{assert_eq!(NBO_MUL_CALLS,1);assert_eq!(NBO_MUL_X,input);assert_eq!(NBO_MUL_Y.0,node);assert_eq!(basis[i],if i==n+j {NBO_MUL_OUT}else{old});}
 kani::cover!(n==1);kani::cover!(n==128);kani::cover!(j==127);kani::cover!(i==n+j);kani::cover!(i!=n+j);
}
#[kani::proof]
#[kani::unwind(4096)]
fn NBO_range_next_bounded(){
 let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=256);kani::assume(end<=256);
 let mut iter=start..end;let result=iter.next();
 if start<end {assert_eq!(result,Some(start));assert_eq!(iter.start,start+1);}
 else {assert_eq!(result,None);assert_eq!(iter.start,start);}
 assert_eq!(iter.end,end);
 kani::cover!(start==0&&end==128);kani::cover!(start==end);kani::cover!(start>end);
}
#[kani::proof]
#[kani::unwind(4096)]
fn NBO_basis_initializer(){
 let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let n=1usize;
 let i:usize=kani::any();kani::assume(i<256);
 assert_eq!(basis[i],if i==0 {M31::ONE}else{M31::ZERO});assert_eq!(n,1);
 kani::cover!(i==0);kani::cover!(i==255);
}
// ONE outer post-inner continuation. The returned basis is not rebuilt.
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::mul,NBO_m31_canonical_reply)]
fn NBO_basis_outer_after_inner(){
 let mut n:usize=kani::any();kani::assume(n>=1&&n<=32);let oldn=n;
 let mut node:u32=kani::any();kani::assume(node<2147483647);let oldnode=node;
 node=M31(node).mul(M31(node)).double().sub(M31::ONE).0;n*=2;
 assert_eq!(n,2*oldn);assert!(n<=64);assert!(node<2147483647);
 unsafe{assert_eq!(NBO_MUL_CALLS,1);assert_eq!(NBO_MUL_X.0,oldnode);assert_eq!(NBO_MUL_Y.0,oldnode);assert_eq!(node,NBO_MUL_OUT.double().sub(M31::ONE).0);}
 kani::cover!(oldn==1);kani::cover!(oldn==32);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
