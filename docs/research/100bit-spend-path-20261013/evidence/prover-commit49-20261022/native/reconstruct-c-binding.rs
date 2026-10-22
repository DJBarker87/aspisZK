
fn reduce_word49(x:u64)->E {call(17,E(x as u32),E((x>>32) as u32))}
fn native_reconstruct_cm49(s:[u64;3])->(E,E) {
 let m0=reduce_word49(s[0]);let m1=reduce_word49(s[1]);let m2=reduce_word49(s[2]);
 (m0.sub(m1),m2.sub(m0).sub(m1))
}
fn owner_reconstruct_cm49(s:[u64;3])->(E,E) {
 let m0=reduce_word49(s[0]);let m1=reduce_word49(s[1]);let m2=reduce_word49(s[2]);
 let a=m0.sub(m1);let b0=m2.sub(m0);let b=b0.sub(m1);(a,b)
}
#[cfg(kani)] mod reconstruct_c_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(40)] fn complete_cm_reconstruction() {
  let s:[u64;3]=kani::any();let answers=kani::any();
  reset(answers);let x=native_reconstruct_cm49(s);let tx=trace();
  reset(answers);let y=owner_reconstruct_cm49(s);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,6);
 }
}
