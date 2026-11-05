use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn q()->QM31{let w:[u32;4]=kani::any();kani::assume(w.iter().all(|&x|x<2147483647));QM31{c0:aspis_core::field::CM31::new(aspis_core::field::M31(w[0]),aspis_core::field::M31(w[1])),c1:aspis_core::field::CM31::new(aspis_core::field::M31(w[2]),aspis_core::field::M31(w[3]))}}
fn words(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn add_word(a:u32,b:u32)->u32{let sum=a+b;if sum>=2147483647{sum-2147483647}else{sum}}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_boundary_step(){
 let polynomial:[QM31;28]=core::array::from_fn(|_|q());let acc=q();let index:usize=kani::any();kani::assume(index<=28);
 if cfg!(NHG_invert){kani::assume(index<28);}
 let mut iter=polynomial[index..].iter();let part=iter.next().copied();
 let (out,next)=match part{None=>(acc,index),Some(c)=>(acc.add(c),index+1)};
 let limb:usize=kani::any();kani::assume(limb<4);
 let expected=if index==28{words(acc)[limb]}else{add_word(words(acc)[limb],words(polynomial[index])[limb])};
 assert_eq!(next,if index==28{28}else{index+1});assert_eq!(iter.as_slice().len(),28-next);
 assert!(core::ptr::eq(iter.as_slice().as_ptr(),polynomial[next..].as_ptr()));
 assert_eq!(words(out)[limb],expected^if cfg!(NHG_invert){1}else{0});
}
struct Product{calls:usize,left:QM31,right:QM31,reply:QM31}
fn product_cut(a:QM31,b:QM31,log:&mut Product)->QM31{
 assert!(words(a).iter().all(|&x|x<2147483647));assert!(words(b).iter().all(|&x|x<2147483647));
 log.calls+=1;log.left=a;log.right=b;log.reply
}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_value_step(){
 let polynomial:[QM31;28]=core::array::from_fn(|_|q());let alpha:[QM31;10]=core::array::from_fn(|_|q());let round:usize=kani::any();kani::assume(round<10);
 let acc=q();let index:usize=kani::any();kani::assume(index<=28);let reply=q();let mut log=Product{calls:0,left:QM31::ZERO,right:QM31::ZERO,reply};
 if cfg!(NHG_invert){kani::assume(index>0);}
 let mut iter=polynomial[..index].iter().rev();let part=iter.next().copied();
 // Exact reverse-fold closure, with only the product replaced by its local log.
 let (out,next)=match part{None=>(acc,0),Some(c)=>{let product=product_cut(acc,alpha[round],&mut log);(product.add(c),index-1)}};
 let limb:usize=kani::any();kani::assume(limb<4);
 let expected=if index==0{words(acc)[limb]}else{add_word(words(reply)[limb],words(polynomial[index-1])[limb])};
 assert_eq!(next,if index==0{0}else{index-1});assert_eq!(iter.len(),next);assert_eq!(log.calls,if index==0{0}else{1});
 if index>0{assert_eq!(words(log.left)[limb],words(acc)[limb]);assert_eq!(words(log.right)[limb],words(alpha[round])[limb]);}
 assert_eq!(words(out)[limb],expected^if cfg!(NHG_invert){1}else{0});
}
