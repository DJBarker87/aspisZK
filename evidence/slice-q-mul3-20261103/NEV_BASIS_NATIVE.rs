// Local opaque product call. No native multiplication executes here; each
// specialization is paired with NEI_PrefixProduct.actual (ALL raw M31 words).
#[derive(Default)]
struct NEV_BasisProductLog { called:bool, lhs:u32, rhs:u32, reply:u32 }
impl NEV_BasisProductLog {
 fn call(&mut self,left:M31,right:M31)->M31 {
  assert!(!self.called);
  self.called=true;self.lhs=left.0;self.rhs=right.0;
  M31(self.reply)
 }
}
// ONE native inner iteration at an arbitrary pre-state and arbitrary observed
// frame cell. Source body's only replacement is product -> local call record.
// No full-array duplication; the actual 256-cell carrier is retained.
#[kani::proof] #[kani::unwind(260)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn basis_inner_iteration() {
 let mut basis:[M31;256]=kani::any();
 let node=M31(kani::any());let n:usize=kani::any();let j:usize=kani::any();
 kani::assume(n>0 && n<=32 && j<n);
 let observed:usize=kani::any();kani::assume(observed<256);
 let before=basis[observed].0;let operand=basis[j].0;
 let mut product=NEV_BasisProductLog {reply:kani::any(),..Default::default()};
 kani::assume(product.reply<2147483647);
 let mut iter=j..n;
 let selected=iter.next().unwrap();
 basis[n+selected]=product.call(basis[selected],node);
 assert!(product.called && product.lhs==operand && product.rhs==node.0);
 assert!(iter.start==j+1 && iter.end==n);
 let expected=if observed==n+j{product.reply}else{before};
 assert_eq!(basis[observed].0,if cfg!(NEV_wrong_basis_inner){expected^1}else{expected});
}
// ONE outer scalar update after its inner loop: square is the sole opaque
// operation. The actual M31::double and M31::sub execute on its canonical reply.
#[kani::proof] #[kani::unwind(64)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn basis_outer_scalar() {
 let mut node=M31(kani::any());let original=node.0;
 let mut n:usize=kani::any();kani::assume(n>0 && n<=32);let old_n=n;
 let mut product=NEV_BasisProductLog {reply:kani::any(),..Default::default()};
 kani::assume(product.reply<2147483647);
 node=product.call(node,node).double().sub(M31::ONE);n*=2;
 assert!(product.called && product.lhs==original && product.rhs==original);
 assert_eq!(n,old_n+old_n);
 let twice=product.reply+product.reply;
 let reduced=if twice>=2147483647{twice-2147483647}else{twice};
 let expected=if reduced==0{2147483646}else{reduced-1};
 assert_eq!(node.0,if cfg!(NEV_wrong_basis_outer){expected^1}else{expected});
 assert!(node.0<2147483647);
}
