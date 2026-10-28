use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]struct NCA_Digest;
static mut NCA_ENABLED:bool=false;static mut NCA_MODE:u8=0;static mut NCA_STAGE:usize=0;static mut NCA_INDEX:usize=0;
static mut NCA_STATES:[[u8;32];5]=[[0;32];5];static mut NCA_SEM_STATE:[u8;32]=[0;32];static mut NCA_SERIALIZED:[u8;32]=[0;32];static mut NCA_INACTIVE:E=E::ZERO;
static mut NCA_Y:*const u8=core::ptr::null();static mut NCA_R0:*const u8=core::ptr::null();static mut NCA_ROOT:*const u8=core::ptr::null();static mut NCA_FINAL:*const u8=core::ptr::null();static mut NCA_PAYLOAD:*const u8=core::ptr::null();
impl Digest32 for NCA_Digest{fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
 if !NCA_ENABLED{return kani::any();}assert_eq!(NCA_MODE,0);assert_eq!(NCA_STAGE,0);assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),29);assert_eq!(parts[1].len(),1);assert_eq!(parts[1][0],2);assert_eq!(parts[2].len(),32);
 let j:usize=kani::any();kani::assume(j<29);assert_eq!(parts[0][j],b"UNPROVED:R1:PRIVATE-SALTED:P3"[j]);assert_eq!(parts[2][NCA_INDEX],NCA_SEM_STATE[NCA_INDEX]);NCA_STAGE=1;NCA_STATES[0]
}}}
fn NCA_scalar<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8],nonzero:bool)->E{unsafe{
 assert!(NCA_STAGE>=1&&NCA_STAGE<=4);let k=NCA_STAGE-1;assert_eq!(row,27+k as u8);assert_eq!(nonzero,k==0);assert_eq!(t.state[NCA_INDEX],NCA_STATES[k][NCA_INDEX]);
 if k==0{assert_eq!(payload.as_ptr(),NCA_Y);assert_eq!(payload.len(),928);}
 if k==1{assert_eq!(payload.len(),32);assert_eq!(payload[NCA_INDEX],NCA_SERIALIZED[NCA_INDEX]);}
 if k==2{assert_eq!(payload.as_ptr(),NCA_R0);assert_eq!(payload.len(),224);}
 if k==3{assert_eq!(payload.as_ptr(),NCA_PAYLOAD);assert_eq!(payload.len(),256);}
 t.state=NCA_STATES[k+1];NCA_STAGE+=1;core::mem::transmute::<[u8;32],E>(kani::any())
}}
fn NCA_serialize_cut(value:E)->[u8;32]{unsafe{assert_eq!(NCA_MODE,0);assert_eq!(NCA_STAGE,2);assert_ne!(value,NCA_INACTIVE);kani::cover!(true,"actual salted seed/gamma reach SAME inactive serializer");kani::assume(false);[0;32]}}
fn NCA_extend_cut<T:Copy,A:alloc::alloc::Allocator>(dst:&mut alloc::vec::Vec<T,A>,src:&[T]){unsafe{assert_eq!(NCA_MODE,1);assert_eq!(NCA_STAGE,4);assert_eq!(core::mem::size_of::<T>(),1);assert_eq!(dst.len(),0);assert_eq!(dst.capacity(),256);assert_eq!(src.len(),32);assert_eq!(src.as_ptr() as *const u8,NCA_ROOT);kani::cover!(true,"kappa/alpha0 reach SAME first append carrier and root");kani::assume(false);}}
fn NCA_queries<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8])->Result<[u32;22],Error>{unsafe{assert_eq!(NCA_MODE,2);assert_eq!(NCA_STAGE,5);assert_eq!(row,31);assert_eq!(payload.as_ptr(),NCA_FINAL);assert_eq!(payload.len(),2048);assert_eq!(t.state[NCA_INDEX],NCA_STATES[4][NCA_INDEX]);NCA_STAGE=6;Err(Error::Transcript)}}
fn NCA_after_serialized<H:Digest32>(v:&View<'_>,mut t:Transcript<H>,serialized:[u8;32])->Result<(),Error>{
 let _kappa=t.scalar(28,&serialized,false);let alpha0=t.scalar(29,v.round0,false);
 let (_alpha,_row)=if v.variant.folds()==2{let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);([alpha0,t.scalar(30,&bytes,false)],31)}else{([alpha0,E::ZERO],30)};
 assert!(false,"first append cut must terminate this S2 branch");Err(Error::Parse)
}
fn NCA_after_appended<H:Digest32>(v:&View<'_>,mut t:Transcript<H>,owned:Vec<u8>,alpha0:E)->Result<Box<Prepared>,Error>{
 // Preserve the original branch-local Vec destruction BEFORE queries.
 let (_alpha,row)={let bytes=owned;([alpha0,t.scalar(30,&bytes,false)],31)};
 let _queries=t.queries(row,v.final_message)?;assert!(false,"query rejection stops this source suffix");Err(Error::Parse)
}
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(crate::transcript::Transcript::scalar,NCA_scalar)]
#[kani::stub(crate::transcript::Transcript::queries,NCA_queries)]
#[kani::stub(aspis_core::field::WideExact::to_le_bytes,NCA_serialize_cut)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NCA_extend_cut)]
fn NCA_inactive_position_wrong(){
 let mode:u8=0;let index:usize=kani::any();kani::assume(mode<3&&index<32);let q=K::ZERO;let point=SecureCirclePoint{x:q,y:q};unsafe{NCA_ENABLED=false;}
 let sem=crate::r1_semantic::Verified{roots:kani::any(),challenges:crate::r1_wire::Challenges{lambda:q,chi:q,theta:q,zc:[q;10],mu:q,eta:q},alpha:[q;10],claims:Box::new([[q;29];3]),extra:[q;29],before_z1:[q;29],state_before_z0:kani::any(),z:[point;2],transcript:crate::r1_wire::SemanticTranscript::new(NCA_Digest,&[],&kani::any()).unwrap()};
 let y:[u8;928]=kani::any();let r0:[u8;224]=kani::any();let r1:[u8;224]=kani::any();let root:[u8;32]=kani::any();let final_message:[u8;2048]=kani::any();let inactive:E=unsafe{core::mem::transmute::<[u8;32],E>(kani::any())};
 let v=View{variant:Variant::S2,semantic:&[],y1:&y,inactive,round0:&r0,folded_root:Some(&root),round1:&r1,final_message:&final_message,query_bytes:&[]};let serialized:[u8;32]=kani::any();
 let mut t=Transcript::new(NCA_Digest,kani::any(),Variant::S2);let mut g:[E;29]=unsafe{core::mem::transmute::<[u8;928],[E;29]>(kani::any())};let old=g;let slot:usize=kani::any();kani::assume(slot<29);
 unsafe{NCA_MODE=mode;NCA_INDEX=index;NCA_STATES=core::mem::transmute::<[u8;160],[[u8;32];5]>(kani::any());NCA_SEM_STATE=sem.transcript.state();NCA_SERIALIZED=serialized;NCA_INACTIVE=inactive;NCA_Y=y.as_ptr();NCA_R0=r0.as_ptr();NCA_ROOT=root.as_ptr();NCA_FINAL=final_message.as_ptr();}
 if mode==0{unsafe{NCA_STAGE=0;NCA_ENABLED=true;}let _=Prepared::new(&sem,&v,NCA_Digest,&mut g);assert!(false,"serializer argument cut must terminate");}
 else if mode==1{unsafe{NCA_STAGE=2;NCA_ENABLED=true;t.state=NCA_STATES[1];}let _=NCA_after_serialized(&v,t,serialized);assert!(false,"append argument cut must terminate");}
 else if mode==2{let ptr=Box::into_raw(Box::new(kani::any::<[u8;256]>())) as *mut u8;let bytes=unsafe{Vec::from_raw_parts(ptr,256,256)};unsafe{NCA_STAGE=4;NCA_ENABLED=true;t.state=NCA_STATES[3];NCA_PAYLOAD=bytes.as_ptr();}let result=NCA_after_appended(&v,t,bytes,E::ZERO);match result{Err(Error::Transcript)=>(),_=>assert!(false,"wrong query rejection")};assert_eq!(g[slot],old[slot]);unsafe{assert_eq!(NCA_STAGE,6);}kani::cover!(true,"alpha1 post-state reaches SAME query after exact Vec drop position");}
}
