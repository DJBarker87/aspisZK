
mod scan_gate {
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct C{a:u32,b:u32}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct K{c0:C,c1:C}
impl K{const ZERO:K=K{c0:C{a:0,b:0},c1:C{a:0,b:0}};const ONE:K=K{c0:C{a:1,b:0},c1:C{a:0,b:0}};}
fn native_width(point:&[K;10])->usize{
 let trailing_boolean=point.iter().rev().take_while(|value|**value==K::ZERO || **value==K::ONE).count();
 point.len()-trailing_boolean
}
fn boolean(x:K)->bool{x.c0.b==0 && x.c1.a==0 && x.c1.b==0 && (x.c0.a==0 || x.c0.a==1)}
fn one(x:K)->bool{x.c0.a==1 && x.c0.b==0 && x.c1.a==0 && x.c1.b==0}
fn owner_width(point:[K;10],left:u8)->u8{
 if left==0{0}else{let n=left-1;let value=point[usize::from(n)];if boolean(value){owner_width(point,n)}else{left}}
}
fn native_suffix(point:&[K;10],width:usize)->usize{
 let mut suffix=0;for coordinate in &point[width..]{suffix=(suffix<<1)|usize::from(*coordinate==K::ONE);}suffix
}
fn owner_suffix(point:[K;10],start:usize,left:u8)->usize{
 if left==0{0}else{let n=left-1;let prev=owner_suffix(point,start,n);let value=point[start.wrapping_add(usize::from(n))];prev.wrapping_shl(1)|usize::from(one(value))}
}
#[cfg(kani)]mod proofs{use super::*;
 #[kani::proof] #[kani::unwind(16)]fn scan(){
 let raw:[[u32;4];10]=kani::any();let p=raw.map(|r|K{c0:C{a:r[0],b:r[1]},c1:C{a:r[2],b:r[3]}});
 let w=native_width(&p);assert_eq!(w,usize::from(owner_width(p,10)));
 let width:u8=kani::any();kani::assume(width<=10);
 assert_eq!(native_suffix(&p,usize::from(width)),owner_suffix(p,usize::from(width),10-width));
 }
}
}
