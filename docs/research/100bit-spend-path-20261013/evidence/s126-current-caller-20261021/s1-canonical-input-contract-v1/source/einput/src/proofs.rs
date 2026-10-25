use aspis_core::field::WideExact as E;
fn canonical(value:&E)->bool{let w=value.to_limbs();
 w[0]<0x7fff_ffff && w[1]<0x7fff_ffff && w[2]<0x7fff_ffff && w[3]<0x7fff_ffff &&
 w[4]<0x7fff_ffff && w[5]<0x7fff_ffff && w[6]<0x7fff_ffff && w[7]<0x7fff_ffff}
#[kani::ensures(|r:&E| canonical(r))]
fn any_e()->E{
 let mut words=[0u32;8];let mut j=0;
 while j<8{let x=kani::any::<u32>()&0x7fff_ffff;words[j]=if x==0x7fff_ffff{0}else{x};j+=1;}
 E::from_limbs(words).unwrap()
}
#[kani::proof_for_contract(any_e)]
fn canonical_generator_contract(){let _=any_e();}
#[kani::proof]
#[kani::stub_verified(any_e)]
fn canonical_generator_use(){let value=any_e();assert!(canonical(&value));}
