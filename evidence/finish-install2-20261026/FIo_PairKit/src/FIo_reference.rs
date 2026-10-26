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
pub fn select_add<A:Arithmetic>(weight:A::E,challenge:A::E,mask:u16,bit:u32)->A::E {
 if mask&(1<<bit)!=0 {A::add(weight,challenge)}else{weight}
}
pub fn subset<A:Arithmetic>(low:[A::E;16],mask:u16)->A::E {
 let weight=A::zero();
 let weight=select_add::<A>(weight,low[0],mask,0);
 let weight=select_add::<A>(weight,low[1],mask,1);
 let weight=select_add::<A>(weight,low[2],mask,2);
 let weight=select_add::<A>(weight,low[3],mask,3);
 let weight=select_add::<A>(weight,low[4],mask,4);
 let weight=select_add::<A>(weight,low[5],mask,5);
 let weight=select_add::<A>(weight,low[6],mask,6);
 let weight=select_add::<A>(weight,low[7],mask,7);
 let weight=select_add::<A>(weight,low[8],mask,8);
 let weight=select_add::<A>(weight,low[9],mask,9);
 let weight=select_add::<A>(weight,low[10],mask,10);
 let weight=select_add::<A>(weight,low[11],mask,11);
 let weight=select_add::<A>(weight,low[12],mask,12);
 let weight=select_add::<A>(weight,low[13],mask,13);
 let weight=select_add::<A>(weight,low[14],mask,14);
 let weight=select_add::<A>(weight,low[15],mask,15);
 weight
}
pub fn contract<A:Arithmetic>(coefficients:[A::E;12],low:[A::E;16])->A::E {
 let pair=A::zero();
 let weight=subset::<A>(low,MASKS[0]);
 let pair=A::add(pair,A::mul(coefficients[0],weight));
 let weight=subset::<A>(low,MASKS[1]);
 let pair=A::add(pair,A::mul(coefficients[1],weight));
 let weight=subset::<A>(low,MASKS[2]);
 let pair=A::add(pair,A::mul(coefficients[2],weight));
 let weight=subset::<A>(low,MASKS[3]);
 let pair=A::add(pair,A::mul(coefficients[3],weight));
 let weight=subset::<A>(low,MASKS[4]);
 let pair=A::add(pair,A::mul(coefficients[4],weight));
 let weight=subset::<A>(low,MASKS[5]);
 let pair=A::add(pair,A::mul(coefficients[5],weight));
 let weight=subset::<A>(low,MASKS[6]);
 let pair=A::add(pair,A::mul(coefficients[6],weight));
 let weight=subset::<A>(low,MASKS[7]);
 let pair=A::add(pair,A::mul(coefficients[7],weight));
 let weight=subset::<A>(low,MASKS[8]);
 let pair=A::add(pair,A::mul(coefficients[8],weight));
 let weight=subset::<A>(low,MASKS[9]);
 let pair=A::add(pair,A::mul(coefficients[9],weight));
 let weight=subset::<A>(low,MASKS[10]);
 let pair=A::add(pair,A::mul(coefficients[10],weight));
 let weight=subset::<A>(low,MASKS[11]);
 let pair=A::add(pair,A::mul(coefficients[11],weight));
 pair
}
pub fn grouped<A:Arithmetic>(f:&[u8],low:[A::E;16])->A::E {
 let coefficients=[A::zero();12];
 let coefficients=coefficient::<A>(coefficients,0,A::field(f,0));
 let coefficients=coefficient::<A>(coefficients,1,A::field(f,1));
 let coefficients=coefficient::<A>(coefficients,2,A::field(f,2));
 let coefficients=coefficient::<A>(coefficients,3,A::field(f,3));
 let coefficients=coefficient::<A>(coefficients,4,A::field(f,4));
 let coefficients=coefficient::<A>(coefficients,5,A::field(f,5));
 let coefficients=coefficient::<A>(coefficients,6,A::field(f,6));
 let coefficients=coefficient::<A>(coefficients,7,A::field(f,7));
 let coefficients=coefficient::<A>(coefficients,8,A::field(f,8));
 let coefficients=coefficient::<A>(coefficients,9,A::field(f,9));
 let coefficients=coefficient::<A>(coefficients,10,A::field(f,10));
 let coefficients=coefficient::<A>(coefficients,11,A::field(f,11));
 let coefficients=coefficient::<A>(coefficients,12,A::field(f,12));
 let coefficients=coefficient::<A>(coefficients,13,A::field(f,13));
 let coefficients=coefficient::<A>(coefficients,14,A::field(f,14));
 let coefficients=coefficient::<A>(coefficients,15,A::field(f,15));
 let coefficients=coefficient::<A>(coefficients,16,A::field(f,16));
 let coefficients=coefficient::<A>(coefficients,17,A::field(f,17));
 let coefficients=coefficient::<A>(coefficients,18,A::field(f,18));
 let coefficients=coefficient::<A>(coefficients,19,A::field(f,19));
 let coefficients=coefficient::<A>(coefficients,20,A::field(f,20));
 let coefficients=coefficient::<A>(coefficients,21,A::field(f,21));
 let coefficients=coefficient::<A>(coefficients,22,A::field(f,22));
 let coefficients=coefficient::<A>(coefficients,23,A::field(f,23));
 let coefficients=coefficient::<A>(coefficients,24,A::field(f,24));
 let coefficients=coefficient::<A>(coefficients,25,A::field(f,25));
 let coefficients=coefficient::<A>(coefficients,26,A::field(f,26));
 let coefficients=coefficient::<A>(coefficients,27,A::field(f,27));
 let coefficients=coefficient::<A>(coefficients,28,A::field(f,28));
 let coefficients=coefficient::<A>(coefficients,29,A::field(f,29));
 let coefficients=coefficient::<A>(coefficients,30,A::field(f,30));
 let coefficients=coefficient::<A>(coefficients,31,A::field(f,31));
 let coefficients=coefficient::<A>(coefficients,32,A::field(f,32));
 let coefficients=coefficient::<A>(coefficients,33,A::field(f,33));
 let coefficients=coefficient::<A>(coefficients,34,A::field(f,34));
 let coefficients=coefficient::<A>(coefficients,35,A::field(f,35));
 let coefficients=coefficient::<A>(coefficients,36,A::field(f,36));
 let coefficients=coefficient::<A>(coefficients,37,A::field(f,37));
 let coefficients=coefficient::<A>(coefficients,38,A::field(f,38));
 let coefficients=coefficient::<A>(coefficients,39,A::field(f,39));
 let coefficients=coefficient::<A>(coefficients,40,A::field(f,40));
 let coefficients=coefficient::<A>(coefficients,41,A::field(f,41));
 let coefficients=coefficient::<A>(coefficients,42,A::field(f,42));
 let coefficients=coefficient::<A>(coefficients,43,A::field(f,43));
 let coefficients=coefficient::<A>(coefficients,44,A::field(f,44));
 let coefficients=coefficient::<A>(coefficients,45,A::field(f,45));
 let coefficients=coefficient::<A>(coefficients,46,A::field(f,46));
 let coefficients=coefficient::<A>(coefficients,47,A::field(f,47));
 let coefficients=coefficient::<A>(coefficients,48,A::field(f,48));
 let coefficients=coefficient::<A>(coefficients,49,A::field(f,49));
 let coefficients=coefficient::<A>(coefficients,50,A::field(f,50));
 let coefficients=coefficient::<A>(coefficients,51,A::field(f,51));
 let coefficients=coefficient::<A>(coefficients,52,A::field(f,52));
 let coefficients=coefficient::<A>(coefficients,53,A::field(f,53));
 let coefficients=coefficient::<A>(coefficients,54,A::field(f,54));
 let coefficients=coefficient::<A>(coefficients,55,A::field(f,55));
 let coefficients=coefficient::<A>(coefficients,56,A::field(f,56));
 let coefficients=coefficient::<A>(coefficients,57,A::field(f,57));
 let coefficients=coefficient::<A>(coefficients,58,A::field(f,58));
 let coefficients=coefficient::<A>(coefficients,59,A::field(f,59));
 let coefficients=coefficient::<A>(coefficients,60,A::field(f,60));
 let coefficients=coefficient::<A>(coefficients,61,A::field(f,61));
 let coefficients=coefficient::<A>(coefficients,62,A::field(f,62));
 let coefficients=coefficient::<A>(coefficients,63,A::field(f,63));
 contract::<A>(coefficients,low)
}
