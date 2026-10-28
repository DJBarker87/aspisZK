use super::*;
// Exact frozen continuing suffix; only Self is renamed to its concrete owner.
fn NBA_tail<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,g:&mut[E;29],gamma:E,kappa:E,alpha:[E;2],rho:K,queries:[u32;22],t:Transcript<H>)->Result<Box<Prepared>,Error>{
        *g=powers::<29>(gamma);
        let claim=prepared_claim(sem,v.y1,v.inactive,g,kappa)?;
        Ok(Box::new(Prepared{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
}

#[derive(Clone,Copy)] struct NBA_Digest;
impl Digest32 for NBA_Digest { fn digest(&self,_parts:&[&[u8]])->[u8;32]{kani::any()} }
// Return overapproximations, not arithmetic contracts. All raw field limbs,
// both Result arms and every state reply are admitted. No output equation is
// assumed. These gates check ONLY routing/control/typed returned-field identity.
fn any_e()->E { unsafe {core::mem::transmute::<[u8;32],E>(kani::any())} }
fn any_k()->K { unsafe {core::mem::transmute::<[u8;16],K>(kani::any())} }
static mut EVENT:usize=0;
static mut PREFIX_ONLY:bool=false;
static mut MID_ONLY:bool=false;
static mut CLAIM_ONLY:bool=false;
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
  if PREFIX_ONLY && EVENT==0 {assert_eq!(payload.as_ptr(),YPTR);assert_eq!(payload.len(),YLEN);}
  if PREFIX_ONLY && EVENT==1 {let i:usize=kani::any();kani::assume(i<32);assert_eq!(payload.len(),32);assert_eq!(payload[i],INACTIVE.to_le_bytes()[i]);}
  if PREFIX_ONLY && EVENT==2 {assert_eq!(payload.as_ptr(),R0PTR);assert_eq!(payload.len(),224);}
  if PREFIX_ONLY && EVENT==3 {let i:usize=kani::any();kani::assume(i<256);assert_eq!(payload.len(),256);let expected=if i<32{*ROOTPTR.add(i)}else{*R1PTR.add(i-32)};assert_eq!(payload[i],expected);}
  SCALARS[EVENT]=any_e();let out=SCALARS[EVENT];EVENT+=1;t.state=kani::any();out
 }
}
fn queries<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8])->Result<[u32;22],Error>{
 unsafe {assert_eq!(EVENT,4);assert_eq!(row,31);assert_eq!(payload.as_ptr(),FPTR);assert_eq!(payload.len(),2048);if PREFIX_ONLY{kani::cover!(true,"prefix reaches queries");kani::assume(false);}EVENT+=1;t.state=kani::any();QERR=kani::any();QUERY=kani::any();if QERR{Err(Error::Transcript)}else{Ok(QUERY)}}
}
fn scalar_k<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8])->K{
 unsafe{assert_eq!(EVENT,5);assert_eq!(row,32);assert!(payload.is_empty());EVENT+=1;t.state=kani::any();LAST=t.state;RHO=any_k();RHO}
}
fn powers29<const N:usize>(x:E)->[E;N]{unsafe{assert_eq!(N,29);assert_eq!(EVENT,6);assert_eq!(x,SCALARS[0]);if MID_ONLY{kani::cover!(true,"success reaches powers before scratch write");kani::assume(false);}EVENT+=1;let fields:[E;29]=core::mem::transmute::<[u8;928],[E;29]>(kani::any());let out=*(&fields as *const [E;29] as *const [E;N]);POWERS=fields;out}}
fn claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error>{
 unsafe{assert_eq!(EVENT,7);EVENT+=1;assert_eq!(sem as *const _ as *const (),SEM_PTR as *const ());assert_eq!(y1.as_ptr(),YPTR);assert_eq!(y1.len(),YLEN);assert_eq!(inactive,INACTIVE);assert_eq!(kappa,SCALARS[1]);let i:usize=kani::any();kani::assume(i<29);assert_eq!(g[i],POWERS[i]);if CLAIM_ONLY{kani::cover!(true,"same-carrier native claim call reached");kani::assume(false);}CLAIM=any_e();CERR=kani::any();if CERR{Err(Error::Parse)}else{Ok(CLAIM)}}
}
fn context<const PART:usize>(){
 let q=any_k();let point=SecureCirclePoint{x:any_k(),y:any_k()};
 let sem=crate::r1_semantic::Verified{roots:kani::any(),challenges:crate::r1_wire::Challenges{lambda:q,chi:q,theta:q,zc:[q;10],mu:q,eta:q},alpha:unsafe{core::mem::transmute::<[u8;160],[K;10]>(kani::any())},claims:Box::new(unsafe{core::mem::transmute::<[u8;1392],[[K;29];3]>(kani::any())}),extra:unsafe{core::mem::transmute::<[u8;464],[K;29]>(kani::any())},before_z1:unsafe{core::mem::transmute::<[u8;464],[K;29]>(kani::any())},state_before_z0:kani::any(),z:unsafe{core::mem::transmute::<[u8;64],[SecureCirclePoint;2]>(kani::any())},transcript:crate::r1_wire::SemanticTranscript::new(NBA_Digest,&[],&kani::any()).unwrap()};
 let y:[u8;928]=kani::any();let round0:[u8;224]=kani::any();let round1:[u8;224]=kani::any();let root:[u8;32]=kani::any();let final_message:[u8;2048]=kani::any();
 let v=View{variant:Variant::S2,semantic:&[],y1:&y,inactive:any_e(),round0:&round0,folded_root:Some(&root),round1:&round1,final_message:&final_message,query_bytes:&[]};
 let mut g:[E;29]=unsafe{core::mem::transmute::<[u8;928],[E;29]>(kani::any())};let old=g;let i:usize=kani::any();kani::assume(i<29);
 unsafe{PREFIX_ONLY=PART==3;MID_ONLY=PART==7;CLAIM_ONLY=PART==11;EVENT=0;SEM_PTR=&sem;YPTR=y.as_ptr();YLEN=y.len();INACTIVE=v.inactive;R0PTR=round0.as_ptr();R1PTR=round1.as_ptr();ROOTPTR=root.as_ptr();FPTR=final_message.as_ptr();}
 let result=if (PART>=4 && PART<=6) || (PART>=8 && PART<=11) {
  unsafe {EVENT=if PART>=8{7}else{6};QERR=false;SCALARS=[any_e(),any_e(),any_e(),any_e()];RHO=any_k();QUERY=kani::any();LAST=kani::any();let mut t=Transcript::new(NBA_Digest,sem.transcript.state(),v.variant);t.state=LAST;
   if PART>=8{POWERS=g;NBA_after_scratch(&sem,&v,&mut g,SCALARS[0],SCALARS[1],[SCALARS[2],SCALARS[3]],RHO,QUERY,t)}
   else{NBA_tail(&sem,&v,&mut g,SCALARS[0],SCALARS[1],[SCALARS[2],SCALARS[3]],RHO,QUERY,t)}}
 }else{Prepared::new(&sem,&v,NBA_Digest,&mut g)};
 unsafe{
  if QERR{assert_eq!(EVENT,5);assert!(matches!(result,Err(Error::Transcript)));assert_eq!(g[i],old[i]);kani::cover!(true,"query rejection retains scratch");}
  else{assert_eq!(EVENT,8);assert_eq!(g[i],POWERS[i]);if CERR{assert!(matches!(result,Err(Error::Parse)));kani::cover!(true,"claim rejection retains produced scratch");}
   else{let p=result.unwrap();kani::cover!(true,"success");
    if PART%4==0{assert_eq!(p.variant,Variant::S2);assert_eq!(p.gamma,SCALARS[0]);assert_eq!(p.kappa,SCALARS[1]);assert_eq!(p.alpha[0],SCALARS[2]);assert_eq!(p.alpha[1],SCALARS[3]);}
    if PART%4==1{assert_eq!(p.rho,RHO);assert_eq!(p.claim,CLAIM);let j:usize=kani::any();kani::assume(j<22);assert_eq!(p.queries[j],QUERY[j]);let k:usize=kani::any();kani::assume(k<32);assert_eq!(p.state[k],LAST[k]);}
    if PART%4==2{let r:usize=kani::any();let j:usize=kani::any();kani::assume(r<2&&j<32);assert_eq!(p.roots[r][j],sem.roots[r][j]);let a:usize=kani::any();kani::assume(a<10);assert_eq!(p.semantic_alpha[a],sem.alpha[a]);assert_eq!(p.z[r],sem.z[r]);}
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

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(Transcript::<NBA_Digest>::scalar,scalar)]
#[kani::stub(Transcript::<NBA_Digest>::queries,queries)]
#[kani::stub(Transcript::<NBA_Digest>::scalar_k,scalar_k)]
#[kani::stub(powers::<29>,powers29)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_prefix_to_queries(){context::<3>()}

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(powers::<29>,powers29)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_suffix_challenges(){context::<4>()}

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(powers::<29>,powers29)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_suffix_tail(){context::<5>()}

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(powers::<29>,powers29)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_suffix_semantic_frame(){context::<6>()}

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(Transcript::<NBA_Digest>::scalar,scalar)]
#[kani::stub(Transcript::<NBA_Digest>::queries,queries)]
#[kani::stub(Transcript::<NBA_Digest>::scalar_k,scalar_k)]
#[kani::stub(powers::<29>,powers29)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_middle_to_powers(){context::<7>()}

#[derive(Clone,Copy)] struct NBA_BlockDigest;
static mut BLOCK_EVENT:usize=100;
static mut BLOCK_INDEX:usize=0;
static mut BLOCK_ROW:u8=0;
static mut BLOCK_PAYLOAD:*const u8=core::ptr::null();
static mut BLOCK_LENGTH:usize=0;
static mut BLOCK_INITIAL:[u8;32]=[0;32];
static mut BLOCK_ABSORBED:[u8;32]=[0;32];
static mut BLOCK_READ:[u8;32]=[0;32];
static mut BLOCK_FINAL:[u8;32]=[0;32];
impl Digest32 for NBA_BlockDigest {
 fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
  if BLOCK_EVENT==100{return kani::any();}
  let j=BLOCK_INDEX;
  if BLOCK_EVENT==0{assert_eq!(parts.len(),4);assert_eq!(parts[0].len(),32);assert_eq!(parts[0][j],BLOCK_INITIAL[j]);assert_eq!(parts[1].len(),2);assert_eq!(parts[1][0],0);assert_eq!(parts[1][1],0xa0+BLOCK_ROW);assert_eq!(parts[2].len(),4);assert_eq!(u32::from_le_bytes(parts[2].try_into().unwrap()) as usize,BLOCK_LENGTH);assert_eq!(parts[3].as_ptr(),BLOCK_PAYLOAD);assert_eq!(parts[3].len(),BLOCK_LENGTH);BLOCK_EVENT=1;BLOCK_ABSORBED}
  else {assert!(BLOCK_EVENT==1||BLOCK_EVENT==2);assert_eq!(parts.len(),2);assert_eq!(parts[0].len(),32);assert_eq!(parts[0][j],BLOCK_ABSORBED[j]);assert_eq!(parts[1].len(),1);assert_eq!(parts[1][0],BLOCK_EVENT as u8);let out=if BLOCK_EVENT==1{BLOCK_READ}else{BLOCK_FINAL};BLOCK_EVENT+=1;out}
 }}
}
#[kani::proof] #[kani::unwind(3)]
fn NBA_transcript_block(){
 let payload:[u8;2048]=kani::any();let n:usize=kani::any();kani::assume(n<=2048);let row:u8=kani::any();kani::assume(row>=27&&row<=32);let index:usize=kani::any();kani::assume(index<32);
 unsafe{BLOCK_EVENT=100;let mut t=Transcript::new(NBA_BlockDigest,kani::any(),Variant::S2);BLOCK_INDEX=index;BLOCK_ROW=row;BLOCK_INITIAL=kani::any();BLOCK_ABSORBED=kani::any();BLOCK_READ=kani::any();BLOCK_FINAL=kani::any();BLOCK_PAYLOAD=payload.as_ptr();BLOCK_LENGTH=n;t.state=BLOCK_INITIAL;BLOCK_EVENT=0;
 let block=t.block(row,&payload[..n]);assert_eq!(BLOCK_EVENT,3);assert_eq!(block[index],BLOCK_READ[index]);assert_eq!(t.state[index],BLOCK_FINAL[index]);kani::cover!(true,"block consumes three arbitrary oracle replies");}
}

fn NBA_after_scratch<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,g:&mut[E;29],gamma:E,kappa:E,alpha:[E;2],rho:K,queries:[u32;22],t:Transcript<H>)->Result<Box<Prepared>,Error>{
        let claim=prepared_claim(sem,v.y1,v.inactive,g,kappa)?;
        Ok(Box::new(Prepared{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
}

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_postwrite_challenges(){context::<8>()}

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_postwrite_tail(){context::<9>()}

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_postwrite_semantic_frame(){context::<10>()}

fn NBA_write(g:&mut[E;29],gamma:E){*g=powers::<29>(gamma);}
#[kani::proof] #[kani::unwind(33)]
#[kani::stub(powers::<29>,powers29)]
fn NBA_scratch_write(){
 let gamma=any_e();let mut g:[E;29]=unsafe{core::mem::transmute::<[u8;928],[E;29]>(kani::any())};
 unsafe{MID_ONLY=false;EVENT=6;SCALARS[0]=gamma;}
 // Frozen suffix's first statement, isolated from subsequent native calls.
 NBA_write(&mut g,gamma);
 let i:usize=kani::any();kani::assume(i<29);unsafe{assert_eq!(EVENT,7);assert_eq!(g[i],POWERS[i]);kani::cover!(true,"all scratch positions overwritten");}
}
// Split record construction from the claim-call cut. These are the frozen
// initializer's named fields, with sem.roots/alpha/z and t.state supplied as
// typed values by the caller. No scalar/arithmetic property is assumed.
fn NBA_record(variant:Variant,roots:[[u8;32];2],gamma:E,kappa:E,alpha:[E;2],rho:K,queries:[u32;22],semantic_alpha:[K;10],z:[SecureCirclePoint;2],claim:E,state:[u8;32])->Box<Prepared>{
 Box::new(Prepared{variant,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state})
}
fn NBA_record_context<const PART:usize>(){
 let roots:[[u8;32];2]=kani::any();let gamma=any_e();let kappa=any_e();let alpha:[E;2]=unsafe{core::mem::transmute::<[u8;64],[E;2]>(kani::any())};let rho=any_k();let queries:[u32;22]=unsafe{core::mem::transmute::<[u8;88],[u32;22]>(kani::any())};let semantic_alpha:[K;10]=unsafe{core::mem::transmute::<[u8;160],[K;10]>(kani::any())};let z:[SecureCirclePoint;2]=unsafe{core::mem::transmute::<[u8;64],[SecureCirclePoint;2]>(kani::any())};let claim=any_e();let state:[u8;32]=kani::any();
 let p=NBA_record(Variant::S2,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state);
 if PART==0{assert_eq!(p.variant,Variant::S2);assert_eq!(p.gamma,gamma);assert_eq!(p.kappa,kappa);let a:usize=kani::any();kani::assume(a<2);assert_eq!(p.alpha[a],alpha[a]);}
 if PART==1{assert_eq!(p.rho,rho);assert_eq!(p.claim,claim);let i:usize=kani::any();kani::assume(i<22);assert_eq!(p.queries[i],queries[i]);let j:usize=kani::any();kani::assume(j<32);assert_eq!(p.state[j],state[j]);}
 if PART==2{let r:usize=kani::any();let j:usize=kani::any();kani::assume(r<2&&j<32);assert_eq!(p.roots[r][j],roots[r][j]);let a:usize=kani::any();kani::assume(a<10);assert_eq!(p.semantic_alpha[a],semantic_alpha[a]);assert_eq!(p.z[r],z[r]);}
 kani::cover!(true,"typed record returned through actual Box");
}
#[kani::proof] #[kani::unwind(33)] fn NBA_record_challenges(){NBA_record_context::<0>()}
#[kani::proof] #[kani::unwind(33)] fn NBA_record_tail(){NBA_record_context::<1>()}
#[kani::proof] #[kani::unwind(33)] fn NBA_record_semantic(){NBA_record_context::<2>()}

#[kani::proof] #[kani::unwind(33)]
#[kani::stub(prepared_claim::<NBA_Digest>,claim)]
fn NBA_claim_call(){context::<11>()}

#[derive(Clone,Copy)] struct NBA_QueryDigest;
static mut QE:usize=100;
static mut QI:usize=0;
static mut QPAY:*const u8=core::ptr::null();
static mut QOLD:[u8;32]=[0;32];
static mut QR:[[u8;32];17]=[[0;32];17];
static mut QRESULT:[u32;22]=[0;22];
static mut QSTATE:[u8;32]=[0;32];
static mut QFAIL:bool=false;
static mut QTERM:bool=false;
impl Digest32 for NBA_QueryDigest{
 fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
  if QE==100{return kani::any();}
  let i=QI;
  if QE==0{assert_eq!(parts.len(),4);assert_eq!(parts[0].len(),32);assert_eq!(parts[0][i],QOLD[i]);assert_eq!(parts[1].len(),2);assert_eq!(parts[1][0],0);assert_eq!(parts[1][1],0xa0+31);assert_eq!(parts[2].len(),4);assert_eq!(u32::from_le_bytes(parts[2].try_into().unwrap()),2048);assert_eq!(parts[3].len(),2048);assert_eq!(parts[3].as_ptr(),QPAY);}
  else{assert!(QE<=16);assert_eq!(parts.len(),2);assert_eq!(parts[0].len(),32);let source=if QE%2==1{QE-1}else{QE-2};assert_eq!(parts[0][i],QR[source][i]);assert_eq!(parts[1].len(),1);assert_eq!(parts[1][0],if QE%2==1{1}else{2});}
  let out=QR[QE];QE+=1;out
 }}
}
fn NBA_query_decode(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>{unsafe{
 assert_eq!(QE,17);let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<8&&j<32);assert_eq!(blocks[k][j],QR[2*k+1][j]);assert_eq!(advances[k][j],QR[2*k+2][j]);
 kani::cover!(true,"all eight eager digest pairs reach decoder");if QTERM{kani::assume(false);}
 QRESULT=core::mem::transmute::<[u8;88],[u32;22]>(kani::any());QSTATE=kani::any();QFAIL=kani::any();
 if QFAIL{Err(aspis_core::transcript::QuerySampleError::DrawLimitExhausted{accepted:kani::any(),max_draws:64})}else{Ok((QRESULT,QSTATE))}
}}
fn NBA_query_context(terminal:bool){
 let payload:[u8;2048]=kani::any();let i:usize=kani::any();kani::assume(i<32);
 unsafe{QE=100;let mut t=Transcript::new(NBA_QueryDigest,kani::any(),Variant::S2);QTERM=terminal;QI=i;QPAY=payload.as_ptr();QOLD=kani::any();QR=core::mem::transmute::<[u8;544],[[u8;32];17]>(kani::any());t.state=QOLD;QE=0;
 let result=t.queries(31,&payload);assert_eq!(QE,17);
 if QFAIL{assert!(matches!(result,Err(Error::Transcript)));assert_eq!(t.state[i],QR[0][i]);kani::cover!(true,"query error retains absorbed state");}
 else{let out=result.unwrap();let j:usize=kani::any();kani::assume(j<22);assert_eq!(out[j],QRESULT[j]);assert_eq!(t.state[i],QSTATE[i]);kani::cover!(true,"query success uses selected decoder state");}
 }
}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,NBA_query_decode)]
fn NBA_query_materialize(){NBA_query_context(true)}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,NBA_query_decode)]
fn NBA_query_result(){NBA_query_context(false)}

#[derive(Clone,Copy)] struct NBA_SeedDigest;
static mut SI:usize=0;static mut SJ:usize=0;static mut SS:[u8;32]=[0;32];static mut SR:[u8;32]=[0;32];static mut SN:usize=0;
impl Digest32 for NBA_SeedDigest{fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
 assert_eq!(SN,0);SN+=1;assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),29);assert_eq!(parts[0][SJ],b"UNPROVED:R1:PRIVATE-SALTED:P3"[SJ]);assert_eq!(parts[1].len(),1);assert_eq!(parts[1][0],2);assert_eq!(parts[2].len(),32);assert_eq!(parts[2][SI],SS[SI]);SR
}}}
#[kani::proof] #[kani::unwind(3)]
fn NBA_transcript_seed(){let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<32&&j<29);unsafe{SI=i;SJ=j;SS=kani::any();SR=kani::any();SN=0;let t=Transcript::new(NBA_SeedDigest,SS,Variant::S2);assert_eq!(SN,1);assert_eq!(t.state[i],SR[i]);kani::cover!(true,"S2 seed framing and arbitrary reply");}}

static mut NBA_RROW:u8=0;static mut NBA_RPTR:*const u8=core::ptr::null();static mut NBA_RLEN:usize=0;
static mut NBA_RI:usize=0;static mut NBA_RMODE:u8=0;static mut NBA_REVENT:usize=0;
static mut NBA_RB:[u8;32]=[0;32];static mut NBA_RBEFORE:[u8;32]=[0;32];static mut NBA_RAFTER:[u8;32]=[0;32];static mut NBA_RE:E=E::ZERO;static mut NBA_RK:K=K::ZERO;
fn NBA_route_block<H:Digest32>(t:&mut Transcript<H>,row:u8,payload:&[u8])->[u8;32]{unsafe{
 assert_eq!(NBA_REVENT,0);NBA_REVENT=1;assert_eq!(row,NBA_RROW);assert_eq!(payload.as_ptr(),NBA_RPTR);assert_eq!(payload.len(),NBA_RLEN);assert_eq!(t.state[NBA_RI],NBA_RBEFORE[NBA_RI]);t.state=NBA_RAFTER;NBA_RB
}}
fn NBA_route_gamma(block:&[u8;32])->E{unsafe{assert_eq!(NBA_REVENT,1);NBA_REVENT=2;assert_eq!(NBA_RMODE,0);assert_eq!(block[NBA_RI],NBA_RB[NBA_RI]);NBA_RE}}
fn NBA_route_ordinary(block:&[u8;32])->E{unsafe{assert_eq!(NBA_REVENT,1);NBA_REVENT=2;assert_eq!(NBA_RMODE,1);assert_eq!(block[NBA_RI],NBA_RB[NBA_RI]);NBA_RE}}
fn NBA_route_qm(block:&[u8;32])->K{unsafe{assert_eq!(NBA_REVENT,1);NBA_REVENT=2;assert_eq!(NBA_RMODE,2);assert_eq!(block[NBA_RI],NBA_RB[NBA_RI]);NBA_RK}}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(crate::transcript::Transcript::block,NBA_route_block)]
#[kani::stub(crate::sampler::gamma_sample,NBA_route_gamma)]
#[kani::stub(crate::sampler::ordinary_sample,NBA_route_ordinary)]
#[kani::stub(crate::sampler::qm31_sample,NBA_route_qm)]
fn NBA_scalar_routes(){
 let payload:[u8;2048]=kani::any();let n:usize=kani::any();let row:u8=kani::any();let i:usize=kani::any();let mode:u8=kani::any();kani::assume(n<=2048&&row>=27&&row<=32&&i<32&&mode<3);let bytes=&payload[..n];
 unsafe{let mut t=Transcript::new(NBA_Digest,kani::any(),Variant::S2);NBA_RROW=row;NBA_RPTR=bytes.as_ptr();NBA_RLEN=n;NBA_RI=i;NBA_RMODE=mode;NBA_REVENT=0;NBA_RBEFORE=kani::any();NBA_RAFTER=kani::any();NBA_RB=kani::any();NBA_RE=any_e();NBA_RK=any_k();t.state=NBA_RBEFORE;
 if mode<2{let x=t.scalar(row,bytes,mode==0);assert_eq!(x.to_le_bytes()[i],NBA_RE.to_le_bytes()[i]);}else{let x=t.scalar_k(row,bytes);let j:usize=kani::any();kani::assume(j<4);assert_eq!([x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0][j],[NBA_RK.c0.a.0,NBA_RK.c0.b.0,NBA_RK.c1.a.0,NBA_RK.c1.b.0][j]);}
 assert_eq!(NBA_REVENT,2);assert_eq!(t.state[i],NBA_RAFTER[i]);kani::cover!(mode==0,"gamma routing");kani::cover!(mode==1,"ordinary routing");kani::cover!(mode==2,"rho routing");
 }
}
