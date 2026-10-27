//! Owned state for the shipped S2 grouped inactive contraction.
//! Arithmetic and byte decoding are explicit callbacks, instantiated separately.
pub trait Arithmetic {
 type E: Copy;
 fn zero()->Self::E;
 fn add(a:Self::E,b:Self::E)->Self::E;
 fn mul(a:Self::E,b:Self::E)->Self::E;
 fn field(bytes:&[u8],i:usize)->Self::E;
}
pub const GROUPS:[u8;64]=[0,1,2,3,4,5,5,6,4,5,5,5,7,7,7,7,7,7,7,4,4,5,5,6,4,5,5,5,7,7,7,4,7,7,7,7,4,5,5,5,4,5,5,5,8,9,10,8,11,2,2,10,4,5,5,6,4,5,5,6,7,7,7,7];
pub const MASKS:[u16;12]=[32769,49217,49280,16448,32767,16383,49151,65535,49152,57344,49216,33024];
pub fn coefficient<A:Arithmetic>(mut coefficients:[A::E;12],j:usize,value:A::E)->[A::E;12] {
 let group=GROUPS[j] as usize;
 coefficients[group]=A::add(coefficients[group],value);
 coefficients
}
pub fn subset<A:Arithmetic>(low:[A::E;16],mask:u16)->A::E {
 let mut weight=A::zero();let mut bit=0usize;
 while bit<16 {
  if mask&(1<<bit)!=0 {weight=A::add(weight,low[bit]);}
  bit+=1;
 }
 weight
}
pub fn contract<A:Arithmetic>(coefficients:[A::E;12],low:[A::E;16])->A::E {
 let mut pair=A::zero();let mut group=0usize;
 while group<12 {
  let weight=subset::<A>(low,MASKS[group]);
  pair=A::add(pair,A::mul(coefficients[group],weight));
  group+=1;
 }
 pair
}
pub fn grouped<A:Arithmetic>(f:&[u8],low:[A::E;16])->A::E {
 let mut coefficients=[A::zero();12];let mut j=0usize;
 while j<64 {
  coefficients=coefficient::<A>(coefficients,j,A::field(f,j));
  j+=1;
 }
 contract::<A>(coefficients,low)
}
