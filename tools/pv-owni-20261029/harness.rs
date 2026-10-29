use aspis_core::field::{QM31 as Q,CM31,M31};
fn q(x:u32)->Q {Q {c0:CM31{a:M31(x%2147483647),b:M31((x.wrapping_mul(37))%2147483647)},c1:CM31{a:M31((x.wrapping_mul(131))%2147483647),b:M31((x.wrapping_mul(251))%2147483647)}}}
fn sparse(col:&[Q],p:&[Q;10])->Option<Q>{
 if col.len()!=1024{return None}
 let mut n=10;while n>0&&(p[n-1]==Q::ZERO||p[n-1]==Q::ONE){n-=1}
 let mut s=0;for v in &p[n..]{s=(s<<1)|usize::from(*v==Q::ONE)}
 let mut w=[(0,Q::ZERO);1024];
 for a in 0..(1<<n){let mut z=Q::ONE;for j in 0..n{z=z.mul(if (a>>(n-1-j))&1==0{Q::ONE.sub(p[j])}else{p[j]});}w[a]=((a<<(10-n))|s,z);}
 let mut z=Q::ZERO;for &(r,x)in &w[..(1<<n)]{z=z.add(x.mul(col[r]));}Some(z)
}
fn dense(col:&[Q],p:&[Q;10])->Option<Q>{
 if col.len()!=1024{return None}
 let mut z=Q::ZERO;
 for r in 0..1024{let mut w=Q::ONE;for j in 0..10{w=w.mul(if (r>>(9-j))&1==0{Q::ONE.sub(p[j])}else{p[j]});}z=z.add(w.mul(col[r]));}Some(z)
}
fn main(){
 assert_eq!(std::mem::size_of::<(usize,Q)>(),24);assert_eq!(std::mem::align_of::<(usize,Q)>(),8);
 assert!(!std::mem::needs_drop::<(usize,Q)>());
 let mut cases=0;
 for width in 0..=10{for suffix in [0,1,341,1023]{for seed in [1u32,17,0x7ffffffe]{
  let p=core::array::from_fn(|i|if i<width{q(seed.wrapping_add(i as u32*997))}else if(suffix>>(9-i))&1==0{Q::ZERO}else{Q::ONE});
  let col:[Q;1024]=core::array::from_fn(|i|q(seed.wrapping_mul(i as u32+1)));
  for len in [0,1,1023,1024]{let c=&col[..len];let got=aspis_statement::constraints_v4::multilinear_evaluate_qm31(c,&p);assert_eq!(got,sparse(c,&p));assert_eq!(got,dense(c,&p));cases+=1;}
 }}}
 // Arbitrary raw limbs: ordered-source equality, with no canonical-field claim.
 for seed in [0u32,0x7fffffff,0x80000000,0xffffffff]{
  let raw=Q{c0:CM31{a:M31(seed),b:M31(seed.rotate_left(1))},c1:CM31{a:M31(seed.rotate_left(9)),b:M31(seed.rotate_left(17))}};
  let p=[raw;10];let col=[raw;1024];assert_eq!(aspis_statement::constraints_v4::multilinear_evaluate_qm31(&col,&p),sparse(&col,&p));cases+=1;
 }
 let v=(0x0102030405060708usize,q(13));let base=&v as *const _ as usize;
 println!("cases={cases} tuple=24/8 pod=true row_offset={} qm_offset={}",&v.0 as *const _ as usize-base,&v.1 as *const _ as usize-base);
}
