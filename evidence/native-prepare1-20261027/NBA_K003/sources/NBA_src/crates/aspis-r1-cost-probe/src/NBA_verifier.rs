use super::*;
#[derive(Clone,Copy)] struct NBA_Digest;
impl Digest32 for NBA_Digest { fn digest(&self,_parts:&[&[u8]])->[u8;32]{kani::any()} }
// Return overapproximations, not arithmetic contracts. All raw field limbs,
// both Result arms and every state reply are admitted. No output equation is
// assumed. These gates check ONLY routing/control/typed returned-field identity.
fn any_e()->E { unsafe {core::mem::transmute::<[u32;8],E>(kani::any())} }
fn any_k()->K { unsafe {core::mem::transmute::<[u32;4],K>(kani::any())} }
static mut EVENT:usize=0;
static mut SCALARS:[E;4]=[E::ZERO;4];
static mut QUERY:[u32;22]=[0;22];
static mut RHO:K=K::ZERO;
static mut LAST:[u8;32]=[0;32];
static mut POWERS:[E;29]=[E::ZERO;29];
static mut CLAIM:E=E::ZERO;
static mut QERR:bool=false;
static mut CERR:bool=false;
static mut SEM_PTR:*const crate::r1_semantic::Verified<NBA_Digest>=core::ptr::null();
static mut YPTR:*const u8=core::ptr::null();
static mut YLEN:usize=0;
static mut INACTIVE:E=E::ZERO;
static mut R0PTR:*const u8=core::ptr::null();
static mut R1PTR:*const u8=core::ptr::null();
static mut ROOTPTR:*const u8=core::ptr::null();
static mut FPTR:*const u8=core::ptr::null();
fn scalar<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8],nonzero:bool)->E {
 unsafe {
  assert!(EVENT<4);assert_eq!(row,27+EVENT as u8);assert_eq!(nonzero,EVENT==0);
  if EVENT==0 {assert_eq!(payload.as_ptr(),YPTR);assert_eq!(payload.len(),YLEN);}
  if EVENT==1 {let i:usize=kani::any();kani::assume(i<32);assert_eq!(payload.len(),32);assert_eq!(payload[i],INACTIVE.to_le_bytes()[i]);}
  if EVENT==2 {assert_eq!(payload.as_ptr(),R0PTR);assert_eq!(payload.len(),224);}
  if EVENT==3 {let i:usize=kani::any();kani::assume(i<256);assert_eq!(payload.len(),256);let expected=if i<32{*ROOTPTR.add(i)}else{*R1PTR.add(i-32)};assert_eq!(payload[i],expected);}
  SCALARS[EVENT]=any_e();let out=SCALARS[EVENT];EVENT+=1;t.state=kani::any();out
 }
}
fn queries<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8])->Result<[u32;22],Error>{
 unsafe {assert_eq!(EVENT,4);assert_eq!(row,31);assert_eq!(payload.as_ptr(),FPTR);assert_eq!(payload.len(),2048);EVENT+=1;t.state=kani::any();QERR=kani::any();QUERY=kani::any();if QERR{Err(Error::Transcript)}else{Ok(QUERY)}}
}
fn scalar_k<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8])->K{
 unsafe{assert_eq!(EVENT,5);assert_eq!(row,32);assert!(payload.is_empty());EVENT+=1;t.state=kani::any();LAST=t.state;RHO=any_k();RHO}
}
fn powers29<const N:usize>(x:E)->[E;N]{unsafe{assert_eq!(N,29);assert_eq!(EVENT,6);assert_eq!(x,SCALARS[0]);EVENT+=1;let out=core::array::from_fn(|_|any_e());POWERS=*(&out as *const [E;N] as *const [E;29]);out}}
fn claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error>{
 unsafe{assert_eq!(EVENT,7);EVENT+=1;assert_eq!(sem as *const _ as *const (),SEM_PTR as *const ());assert_eq!(y1.as_ptr(),YPTR);assert_eq!(y1.len(),YLEN);assert_eq!(inactive,INACTIVE);assert_eq!(kappa,SCALARS[1]);let i:usize=kani::any();kani::assume(i<29);assert_eq!(g[i],POWERS[i]);CLAIM=any_e();CERR=kani::any();if CERR{Err(Error::Parse)}else{Ok(CLAIM)}}
}
fn context<const PART:usize>(){
 let q=any_k();let point=SecureCirclePoint{x:any_k(),y:any_k()};
 let sem=crate::r1_semantic::Verified{roots:kani::any(),challenges:crate::r1_wire::Challenges{lambda:q,chi:q,theta:q,zc:[q;10],mu:q,eta:q},alpha:unsafe{core::mem::transmute::<[[u32;4];10],[K;10]>(kani::any())},claims:Box::new([[q;29];3]),extra:[q;29],before_z1:[q;29],state_before_z0:kani::any(),z:[point;2],transcript:crate::r1_wire::SemanticTranscript::new(NBA_Digest,&[],&kani::any()).unwrap()};
 let y:[u8;928]=kani::any();let round0:[u8;224]=kani::any();let round1:[u8;224]=kani::any();let root:[u8;32]=kani::any();let final_message:[u8;2048]=kani::any();
 let v=View{variant:Variant::S2,semantic:&[],y1:&y,inactive:any_e(),round0:&round0,folded_root:Some(&root),round1:&round1,final_message:&final_message,query_bytes:&[]};
 let mut g:[E;29]=unsafe{core::mem::transmute::<[[u32;8];29],[E;29]>(kani::any())};let old=g;let i:usize=kani::any();kani::assume(i<29);
 unsafe{EVENT=0;SEM_PTR=&sem;YPTR=y.as_ptr();YLEN=y.len();INACTIVE=v.inactive;R0PTR=round0.as_ptr();R1PTR=round1.as_ptr();ROOTPTR=root.as_ptr();FPTR=final_message.as_ptr();}
 let result=Prepared::new(&sem,&v,NBA_Digest,&mut g);
 unsafe{
  if QERR{assert_eq!(EVENT,5);assert!(matches!(result,Err(Error::Transcript)));assert_eq!(g[i],old[i]);kani::cover!(true,"query rejection retains scratch");}
  else{assert_eq!(EVENT,8);assert_eq!(g[i],POWERS[i]);if CERR{assert!(matches!(result,Err(Error::Parse)));kani::cover!(true,"claim rejection retains produced scratch");}
   else{let p=result.unwrap();kani::cover!(true,"success");
    if PART==0{assert_eq!(p.variant,Variant::S2);assert_eq!(p.gamma,SCALARS[0]);assert_eq!(p.kappa,SCALARS[1]);assert_eq!(p.alpha[0],SCALARS[2]);assert_eq!(p.alpha[1],SCALARS[3]);}
    if PART==1{assert_eq!(p.rho,RHO);assert_eq!(p.claim,CLAIM);let j:usize=kani::any();kani::assume(j<22);assert_eq!(p.queries[j],QUERY[j]);let k:usize=kani::any();kani::assume(k<32);assert_eq!(p.state[k],LAST[k]);}
    if PART==2{let r:usize=kani::any();let j:usize=kani::any();kani::assume(r<2&&j<32);assert_eq!(p.roots[r][j],sem.roots[r][j]);let a:usize=kani::any();kani::assume(a<10);assert_eq!(p.semantic_alpha[a],sem.alpha[a]);assert_eq!(p.z[r],sem.z[r]);}
   }
  }
 }
}
#[kani::proof] #[kani::unwind(33)]
#[kani::stub(Transcript::<NBA_Digest>::scalar,scalar)]
#[kani::stub(Transcript::<NBA_Digest>::queries,queries)]
#[kani::stub(Transcript::<NBA_Digest>::scalar_k,scalar_k)]
#[kani::stub(powers::<29>,powers29)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_new_challenges(){context::<0>()}
#[kani::proof] #[kani::unwind(33)]
#[kani::stub(Transcript::<NBA_Digest>::scalar,scalar)]
#[kani::stub(Transcript::<NBA_Digest>::queries,queries)]
#[kani::stub(Transcript::<NBA_Digest>::scalar_k,scalar_k)]
#[kani::stub(powers::<29>,powers29)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_new_tail(){context::<1>()}
#[kani::proof] #[kani::unwind(33)]
#[kani::stub(Transcript::<NBA_Digest>::scalar,scalar)]
#[kani::stub(Transcript::<NBA_Digest>::queries,queries)]
#[kani::stub(Transcript::<NBA_Digest>::scalar_k,scalar_k)]
#[kani::stub(powers::<29>,powers29)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_new_semantic_frame(){context::<2>()}
