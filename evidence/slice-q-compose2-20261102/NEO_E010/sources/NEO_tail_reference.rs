// Safe references for the remaining small scalar/borrowed source cuts.
pub fn checked(index:usize)->Result<usize,u8> {if index<262144{Ok(index)}else{Err(0)}}
pub fn opening(proof:&[u8],i:usize)->&[u8] {let at=10055+i*832;&proof[at..at+832]}
pub trait InverseOps {fn mul(x:u32,y:u32)->u32;fn square(x:u32,count:usize)->u32;}
pub fn inverse<O:InverseOps>(x:u32)->u32 {
 assert!(x!=0,"inverse of zero");
 let t2=O::mul(O::mul(x,x),x);
 let t4=O::mul(O::square(t2,2),t2);
 let t8=O::mul(O::square(t4,4),t4);
 let t16=O::mul(O::square(t8,8),t8);
 let t24=O::mul(O::square(t16,8),t8);
 let t28=O::mul(O::square(t24,4),t4);
 let t29=O::mul(O::mul(t28,t28),x);
 let t30=O::mul(t29,t29);
 O::mul(O::mul(t30,t30),x)
}
