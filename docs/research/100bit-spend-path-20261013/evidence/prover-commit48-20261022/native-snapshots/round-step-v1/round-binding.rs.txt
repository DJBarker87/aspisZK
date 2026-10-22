const PERM:[usize;4]=[0,3,2,1];
fn native_round_step(q:[E;1024],w:[E;1024],mut c:[E;7],d:usize,s:usize,t:usize)->[E;7] {
c[s+PERM[t]]=c[s+PERM[t]].add(q[4*d+s].mul(w[4*d+t]));
 c
}
fn owned_round_step(q:[E;1024],w:[E;1024],mut out:[E;7],d:usize,s:usize,t:usize)->[E;7] {
 let permutation=[0usize,3,2,1];let k=s+permutation[t];
 out[k]=out[k].add(q[4*d+s].mul(w[4*d+t]));out
}
#[cfg(kani)] mod round_proofs {use super::*;
 #[kani::proof] #[kani::unwind(1030)] fn coefficient_iteration() {
 let raw:[u32;1024]=kani::any();let q:[E;1024]=unsafe {core::mem::transmute(raw)};
 let raw:[u32;1024]=kani::any();let w:[E;1024]=unsafe {core::mem::transmute(raw)};
 let raw:[u32;7]=kani::any();let out=raw.map(E);let d:usize=kani::any();let s:usize=kani::any();let t:usize=kani::any();
 kani::assume(d<256 && s<4 && t<4);let answers=kani::any();
 reset(answers);let actual=native_round_step(q,w,out,d,s,t);let ta=trace();
 reset(answers);let expected=owned_round_step(q,w,out,d,s,t);let tb=trace();
 assert_eq!(actual,expected);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
}
