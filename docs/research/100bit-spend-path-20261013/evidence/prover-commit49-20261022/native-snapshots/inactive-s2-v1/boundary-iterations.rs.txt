
#[derive(Clone,Copy)] struct M(u32);
#[derive(Clone,Copy)] struct C { a:M,b:M }
#[derive(Clone,Copy)] struct K { c0:C,c1:C }
fn native_boundary_sums(polynomial:&[K;28])->[u64;4] {
    let first = polynomial[0];
    let mut limbs = [
        2 * u64::from(first.c0.a.0),
        2 * u64::from(first.c0.b.0),
        2 * u64::from(first.c1.a.0),
        2 * u64::from(first.c1.b.0),
    ];
    for coefficient in &polynomial[1..] {
        limbs[0] += u64::from(coefficient.c0.a.0);
        limbs[1] += u64::from(coefficient.c0.b.0);
        limbs[2] += u64::from(coefficient.c1.a.0);
        limbs[3] += u64::from(coefficient.c1.b.0);
    }
    limbs
}
fn owner_boundary_limb(q:[u32;28])->u64 {
 let mut total=2*u64::from(q[0]);
 for i in 1..28 {total+=u64::from(q[i]);}
 total
}
#[cfg(kani)] mod boundary_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(30)] fn complete_limb_accumulation() {
  let raw:[[u32;4];28]=kani::any();
  let q=raw.map(|x|K{c0:C{a:M(x[0]),b:M(x[1])},c1:C{a:M(x[2]),b:M(x[3])}});
  let actual=native_boundary_sums(&q);
  for lane in 0..4 {
   let words=raw.map(|x|x[lane]);
   assert_eq!(actual[lane],owner_boundary_limb(words));
  }
 }
}
