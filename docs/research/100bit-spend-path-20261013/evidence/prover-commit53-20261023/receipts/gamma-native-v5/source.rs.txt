#![allow(unexpected_cfgs)]
type E=[u32;8];
#[derive(Clone,Copy)]
struct Answers { mul:[E;29], add:[E;29] }
#[derive(Clone,Copy,PartialEq,Eq,Debug)]
struct Trace { operands:[[E;4];29], used:usize }
fn operation(t:&mut Trace,p:E,c:E,acc:E,a:&Answers,l:usize)->E {
 t.operands[l]=[p,c,acc,a.mul[l]];t.used+=1;a.add[l]
}
// The native selected-j fold, with every arithmetic operand recorded and
// identical universal answers paired with the extracted counter owner.
fn native(p:[E;29],c:[E;29],a:&Answers,t:&mut Trace)->E {
 (0..29).fold([0;8],|s,l|operation(t,p[l],c[l],s,a,l))
}
fn owner(p:&[E;29],c:&[E;29],a:&Answers,t:&mut Trace,l:usize,left:u8,acc:E)->E {
 if left==0 {acc} else {
  let next=operation(t,p[l],c[l],acc,a,l);
  owner(p,c,a,t,l+1,left-1,next)
 }
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(32)] fn complete_gamma_cell_trace() {
  let p:[E;29]=kani::any();let c:[E;29]=kani::any();
  let a=Answers{mul:kani::any(),add:kani::any()};
  let mut t=Trace{operands:[[[0;8];4];29],used:0};let mut u=t;
  let x=native(p,c,&a,&mut t);let y=owner(&p,&c,&a,&mut u,0,29,[0;8]);
  for i in 0..8 {assert_eq!(x[i],y[i]);}
  for l in 0..29 {for op in 0..4 {for i in 0..8 {assert_eq!(t.operands[l][op][i],u.operands[l][op][i]);}}}
  assert_eq!(t.used,u.used);assert_eq!(t.used,29);
 }
}
#[cfg(kani)] mod iteration_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(32)] fn gamma_iteration_trace() {
  let p:[E;29]=kani::any();let c:[E;29]=kani::any();
  let a=Answers{mul:kani::any(),add:kani::any()};let acc:E=kani::any();
  let l:usize=kani::any();kani::assume(l<29);
  let mut t=Trace{operands:[[[0;8];4];29],used:0};let mut u=t;
  let x=operation(&mut t,p[l],c[l],acc,&a,l);
  let y=owner(&p,&c,&a,&mut u,l,1,acc);
  let i:usize=kani::any();kani::assume(i<8);
  let r:usize=kani::any();kani::assume(r<29);
  let op:usize=kani::any();kani::assume(op<4);
  assert_eq!(x[i],y[i]);assert_eq!(t.operands[r][op][i],u.operands[r][op][i]);
  assert_eq!(t.used,u.used);assert_eq!(t.used,1);
 }
}
