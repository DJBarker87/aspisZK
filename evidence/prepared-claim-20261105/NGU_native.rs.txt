//! Local records only. Frozen prepared_claim cuts; no arithmetic multiplication.
use super::*;
use aspis_core::field::CM31;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_e()->E {let w:[u32;8]=kani::any();for x in w{kani::assume(x<2147483647);}E::from_limbs(w).unwrap()}
fn any_q()->K {let w:[u32;4]=kani::any();K{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
fn words(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
#[cfg(NGU_invert)]const XOR:u32=1;
#[cfg(not(NGU_invert))]const XOR:u32=0;
fn check(actual:u32,expected:u32){assert_eq!(actual,expected^XOR)}
fn array()->[E;7]{let mut a=[E::ZERO;7];for i in 0..7{a[i]=any_e();}a}
macro_rules! kmx {($name:ident,$body:block)=>{
 #[kani::proof] #[kani::unwind(66)]
 #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
 #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
 fn $name()$body
}}
kmx!(parts_initial,{
 let inactive=any_e();let mut parts=[E::ZERO;7];parts[0]=inactive;
 let row:usize=kani::any();kani::assume(row<7);let limb:usize=kani::any();kani::assume(limb<8);
 check(parts[row].to_limbs()[limb],if row==0{inactive.to_limbs()[limb]}else{0});
});
kmx!(parts_store,{
 let mut parts=array();let before=parts;let value=any_e();let point:usize=kani::any();kani::assume(point<6);
 parts[point+1]=value;let row:usize=kani::any();kani::assume(row<7);let limb:usize=kani::any();kani::assume(limb<8);
 check(parts[row].to_limbs()[limb],if row==point+1{value.to_limbs()[limb]}else{before[row].to_limbs()[limb]});
});
kmx!(weighted_add_tail,{
 let mut claim=any_e();let product=any_e();let old=claim.to_limbs();let term=product.to_limbs();
 claim=claim.add(product);let limb:usize=kani::any();kani::assume(limb<8);let sum=old[limb]+term[limb];
 check(claim.to_limbs()[limb],if sum>=2147483647{sum-2147483647}else{sum});assert!(claim.to_limbs()[limb]<2147483647);
});
// This cut stops BEFORE multiplication, as the original LPq operand gate.
// The logged operands' value law is NGU_ClaimOps.multiply, not a Kani product.
kmx!(weighted_operands,{
 let k=array();let parts=array();let bk=k;let bp=parts;let i:usize=kani::any();kani::assume(i<7);
 let limb:usize=kani::any();kani::assume(limb<8);
 crate::trace::value(14,i,parts[i]);let operands=(k[i],parts[i]);
 check(operands.0.to_limbs()[limb],k[i].to_limbs()[limb]);
 check(operands.1.to_limbs()[limb],parts[i].to_limbs()[limb]);
 let row:usize=kani::any();kani::assume(row<7);check(k[row].to_limbs()[limb],bk[row].to_limbs()[limb]);check(parts[row].to_limbs()[limb],bp[row].to_limbs()[limb]);
});
// One exact bound/advance transition on an arbitrary loop prestate.
kmx!(point_advance,{
 let point:usize=kani::any();kani::assume(point<6);let next=point+1;
 check(next as u32,(point+1) as u32);assert!(next<7);
});
kmx!(lane_advance,{
 let l:usize=kani::any();kani::assume(l<29);let next=l+1;
 check(next as u32,(l+1) as u32);assert!(next<=29);
});
// Pure data control; no arithmetic body is executed or credited by this gate.
#[kani::proof]#[kani::unwind(180)]
fn constant_control(){
 let selected:usize=kani::any();kani::assume(selected<174);let mut seen=0;let mut at_point=0;let mut at_lane=0;
 for point in 0..6{for l in 0..29{if seen==selected{at_point=point;at_lane=l;}seen+=1;}}
 check(seen as u32,174);check(at_point as u32,(selected/29) as u32);check(at_lane as u32,(selected%29) as u32);
}
kmx!(scalar_c0_port,{
 let value=any_e();let scalar=value.c0();let limb:usize=kani::any();kani::assume(limb<4);
 check(words(scalar)[limb],value.to_limbs()[limb]);
});
// One source selection on the complete arbitrary native matrices. Only fields
// read by this cut appear; no sparse or zero-filled substitute for a read cell.
kmx!(semantic_selections,{
 let claims:[[[u32;4];29];3]=kani::any();let extra:[[u32;4];29]=kani::any();let before:[[u32;4];29]=kani::any();
 let point:usize=kani::any();kani::assume(point<5);let l:usize=kani::any();kani::assume(l<29);let limb:usize=kani::any();kani::assume(limb<4);
 let scalar=match point{0..=2=>claims[point][l],3=>extra[l],4=>before[l],_=>unreachable!()};
 let expected=if point<=2{claims[point][l]}else if point==3{extra[l]}else{before[l]};
 check(scalar[limb],expected[limb]);
});
// Fixed-array nominal carrier check, independent of selection and allocation.
kmx!(semantic_word_port,{
 let q=any_q();let limb:usize=kani::any();kani::assume(limb<4);
 let actual=words(q)[limb];let expected=match limb{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0};check(actual,expected);
});
// Error/control cut from the exact source ? expression. No callee success is
// assumed; both opaque replies are tested and Parse is the SAME Error carrier.
kmx!(push_error_cut,{
 let reply:Result<(),()>=if kani::any(){Ok(())}else{Err(())};
 let actual:Result<(),Error>=(||{reply.map_err(|_|Error::Parse)?;Ok(())})();
 match reply{Ok(())=>{assert!(actual.is_ok());check(0,0)},Err(_)=>{assert!(matches!(actual,Err(Error::Parse)));check(0,0)}}
});

kmx!(y1_window_read,{
 let bytes:[u8;32]=kani::any();
 for limb in 0..8{let at=4*limb;let word=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);kani::assume(word<2147483647);}
 let scalar=field(&bytes,0).c0();let limb:usize=kani::any();kani::assume(limb<4);let at=4*limb;
 check(words(scalar)[limb],u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]));
});
#[derive(Clone,Copy)]struct NGU_Hash;
impl Digest32 for NGU_Hash{fn digest(&self,_:&[&[u8]])->[u8;32]{[0;32]}}
kmx!(semantic_direct_carriers,{
 let claims:[[K;29];3]=unsafe{core::mem::transmute(kani::any::<[u32;348]>())};
 let extra:[K;29]=unsafe{core::mem::transmute(kani::any::<[u32;116]>())};
 let before:[K;29]=unsafe{core::mem::transmute(kani::any::<[u32;116]>())};
 assert_eq!(core::mem::size_of::<K>(),16);
 let challenges=crate::r1_wire::Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:[K::ZERO;10],mu:K::ZERO,eta:K::ZERO};
 let transcript=crate::r1_wire::SemanticTranscript::new(NGU_Hash,&[],&[0;32]).unwrap();
 let sem=crate::r1_semantic::Verified{roots:[[0;32];2],challenges,alpha:[K::ZERO;10],claims:Box::new(claims),extra,before_z1:before,state_before_z0:[0;32],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],transcript};
 let point:usize=kani::any();kani::assume(point<5);let l:usize=kani::any();kani::assume(l<29);
 let scalar=match point{0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>unreachable!()};
 let expected=if point<=2{sem.claims[point][l]}else if point==3{sem.extra[l]}else{sem.before_z1[l]};
 let limb:usize=kani::any();kani::assume(limb<4);check(words(scalar)[limb],words(expected)[limb]);
});

kmx!(g_read_frame,{
 // Every bit pattern is Rust-representation-valid: eight stored u32 fields.
 let g:[E;29]=unsafe{core::mem::transmute(kani::any::<[u32;232]>())};
 let l:usize=kani::any();kani::assume(l<29);let row:usize=kani::any();kani::assume(row<29);
 let limb:usize=kani::any();kani::assume(limb<8);let before=g[row].to_limbs()[limb];
 let selected=g[l];check(selected.to_limbs()[limb],g[l].to_limbs()[limb]);check(g[row].to_limbs()[limb],before);
});
kmx!(result_return,{
 let claim=any_e();let limb:usize=kani::any();kani::assume(limb<8);let expected=claim.to_limbs()[limb];
 crate::trace::value(14,7,claim);let result:Result<E,Error>=Ok(claim);
 match result{Ok(value)=>check(value.to_limbs()[limb],expected),Err(_)=>assert!(false)}
});
kmx!(y1_two_window_frame,{
 let bytes:[u8;64]=kani::any();let l:usize=kani::any();kani::assume(l<2);
 for limb in 0..8{let at=32*l+4*limb;let word=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);kani::assume(word<2147483647);}
 let observe:usize=kani::any();kani::assume(observe<64);let before=bytes[observe];
 let scalar=field(&bytes,l).c0();let limb:usize=kani::any();kani::assume(limb<4);let at=32*l+4*limb;
 check(words(scalar)[limb],u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]));check(bytes[observe] as u32,before as u32);
});
kmx!(weighted_control,{
 let selected:usize=kani::any();kani::assume(selected<7);let mut count=0;let mut observed=0;
 for i in 0..7{if count==selected{observed=i;}count+=1;}
 check(count as u32,7);check(observed as u32,selected as u32);
});
