use aspis_core::field::WideExact as E;
fn any_e()->E{
 let mut words=[0u32;8];let mut j=0;
 while j<8{let x=kani::any::<u32>()&0x7fff_ffff;words[j]=if x==0x7fff_ffff{0}else{x};j+=1;}
 E::from_limbs(words).unwrap()
}
// All nonselected bytes stay arbitrary. Only the reached field's eight
// canonical words are encoded explicitly, independently of E::to_le_bytes.
#[kani::proof]
#[kani::unwind(33)]
fn selected_field32(){
 let mut bytes=kani::any::<[u8;928]>();let index=(kani::any::<u8>()%29)as usize;
 let expected=any_e();let words=expected.to_limbs();let mut j=0;
 while j<8{let mut b=0;while b<4{bytes[32*index+4*j+b]=(words[j]>>(8*b))as u8;b+=1;}j+=1;}
 let actual=crate::weights::field(&bytes,index);
 let result=actual.to_limbs();j=0;while j<8{assert!(result[j]==words[j]);j+=1;}
 let q=actual.c0();assert!(q.c0.a.0==words[0]);assert!(q.c0.b.0==words[1]);
 assert!(q.c1.a.0==words[2]);assert!(q.c1.b.0==words[3]);
 let r=actual.c1();assert!(r.c0.a.0==words[4]);assert!(r.c0.b.0==words[5]);
 assert!(r.c1.a.0==words[6]);assert!(r.c1.b.0==words[7]);
 kani::cover!(index==0,"first selected32-byte frame");
 kani::cover!(index==28,"last selected32-byte frame");
}
