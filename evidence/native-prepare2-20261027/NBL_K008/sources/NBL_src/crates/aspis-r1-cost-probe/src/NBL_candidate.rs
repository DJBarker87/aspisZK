use super::*;
#[derive(Clone,Copy)] struct NBL_Digest;
static mut NBL_ENABLED:bool=false;
static mut NBL_STAGE:usize=0;
static mut NBL_INDEX:usize=0;
static mut NBL_STATES:[[u8;32];5]=[[0;32];5];
static mut NBL_SEM_STATE:[u8;32]=[0;32];
static mut NBL_Y:*const u8=core::ptr::null();
static mut NBL_R0:*const u8=core::ptr::null();
static mut NBL_R1:*const u8=core::ptr::null();
static mut NBL_ROOT:*const u8=core::ptr::null();
static mut NBL_FINAL:*const u8=core::ptr::null();
impl Digest32 for NBL_Digest { fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
 if !NBL_ENABLED{return kani::any();}
 assert_eq!(NBL_STAGE,0);assert_eq!(parts.len(),3);assert_eq!(parts[2].len(),32);
 assert_eq!(parts[2][NBL_INDEX],NBL_SEM_STATE[NBL_INDEX]);NBL_STAGE=1;NBL_STATES[0]
}}}
fn NBL_scalar<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8],nonzero:bool)->E{unsafe{
 assert!(NBL_STAGE>=1&&NBL_STAGE<=4);let k=NBL_STAGE-1;let i=NBL_INDEX;
 assert_eq!(t.state[i],NBL_STATES[k][i]);assert_eq!(row,27+k as u8);assert_eq!(nonzero,k==0);
 if k==0{assert_eq!(payload.as_ptr(),NBL_Y);assert_eq!(payload.len(),928);}
 if k==1{assert_eq!(payload.len(),32);}
 if k==2{assert_eq!(payload.as_ptr(),NBL_R0);assert_eq!(payload.len(),224);}
 if k==3{let j:usize=kani::any();kani::assume(j<256);assert_eq!(payload.len(),256);assert_eq!(payload[j],if j<32{*NBL_ROOT.add(j)}else{*NBL_R1.add(j-32)});}
 t.state=NBL_STATES[k+1];NBL_STAGE+=1;
 core::mem::transmute::<[u8;32],E>(kani::any())
}}
fn NBL_queries_error<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8])->Result<[u32;22],Error>{unsafe{
 assert_eq!(NBL_STAGE,5);assert_eq!(row,31);assert_eq!(t.state[NBL_INDEX],NBL_STATES[4][NBL_INDEX]);
 assert_eq!(payload.as_ptr(),NBL_FINAL);assert_eq!(payload.len(),2048);NBL_STAGE=6;Err(Error::Transcript)
}}
#[kani::proof] #[kani::unwind(33)]
#[kani::stub(crate::transcript::Transcript::scalar,NBL_scalar)]
#[kani::stub(crate::transcript::Transcript::queries,NBL_queries_error)]
fn NBL_opening_same_state(){
 let q=K::ZERO;let point=SecureCirclePoint{x:q,y:q};
 unsafe{NBL_ENABLED=false;}
 let sem=crate::r1_semantic::Verified{roots:kani::any(),challenges:crate::r1_wire::Challenges{lambda:q,chi:q,theta:q,zc:[q;10],mu:q,eta:q},alpha:[q;10],claims:Box::new([[q;29];3]),extra:[q;29],before_z1:[q;29],state_before_z0:kani::any(),z:[point;2],transcript:crate::r1_wire::SemanticTranscript::new(NBL_Digest,&[],&kani::any()).unwrap()};
 let y:[u8;928]=kani::any();let r0:[u8;224]=kani::any();let r1:[u8;224]=kani::any();let root:[u8;32]=kani::any();let final_message:[u8;2048]=kani::any();
 let v=View{variant:Variant::S2,semantic:&[],y1:&y,inactive:unsafe{core::mem::transmute::<[u8;32],E>(kani::any())},round0:&r0,folded_root:Some(&root),round1:&r1,final_message:&final_message,query_bytes:&[]};
 let mut g:[E;29]=unsafe{core::mem::transmute::<[u8;928],[E;29]>(kani::any())};let old=g;
 let j:usize=kani::any();let i:usize=kani::any();kani::assume(j<29&&i<32);
 unsafe{NBL_INDEX=i;NBL_STAGE=0;NBL_STATES=core::mem::transmute::<[u8;160],[[u8;32];5]>(kani::any());NBL_SEM_STATE=sem.transcript.state();NBL_Y=y.as_ptr();NBL_R0=r0.as_ptr();NBL_R1=r1.as_ptr();NBL_ROOT=root.as_ptr();NBL_FINAL=final_message.as_ptr();NBL_ENABLED=true;}
 let result=Prepared::new(&sem,&v,NBL_Digest,&mut g);
 assert!(matches!(result,Err(Error::Transcript)));assert_eq!(g[j],old[j]);unsafe{assert_eq!(NBL_STAGE,6);}
 kani::cover!(true,"seed and four scalar poststates link to the rejecting query call");
}
