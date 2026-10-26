#![allow(static_mut_refs)]
use super::{Prepared,View,Error};
use alloc::boxed::Box;
use aspis_core::{Digest32,field::{WideExact as E,QM31,CM31,M31},circle::SecureCirclePoint};
use crate::{transport::Variant,r1_semantic::Verified};

#[derive(Clone,Copy)]struct Hash;
impl Digest32 for Hash{fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{digest_step(parts)}}}
static mut DIGEST_CALLS:usize=0;
static mut HASHES:[[u8;32];33]=[[0;32];33];
static mut STAGE:usize=0;
static mut MUL_CALLS:usize=0;
static mut FAIL_AT:u8=2;
static mut ERROR:Error=Error::Parse;
static mut STATES:[[u8;32];7]=[[0;32];7];
static mut SEM_STATE:[u8;32]=[0;32];
static mut SCALARS:[E;4]=[E::ZERO;4];
static mut POWERS:[E;29]=[E::ZERO;29];
static mut QUERY:[u32;22]=[0;22];
static mut RHO:QM31=QM31::ZERO;
static mut CLAIM:E=E::ZERO;
static mut STOP:usize=174;
static mut CPUSH:usize=0;
static mut CFINISH:usize=0;
static mut CFIELD:usize=0;
static mut CADD:usize=0;
static mut KG:[E;7]=[E::ZERO;7];
static mut DOT_RET:[E;6]=[E::ZERO;6];
static mut FIELDS:[E;29]=[E::ZERO;29];
static mut MULTS:[E;7]=[E::ZERO;7];
static mut ADDS:[E;7]=[E::ZERO;7];
static mut DOT_LAST:[u64;8]=[0;8];
static mut DOT_COUNT_LAST:usize=0;
static mut SEM_CLAIMS:[[QM31;29];3]=[[QM31::ZERO;29];3];
static mut SEM_EXTRA:[QM31;29]=[QM31::ZERO;29];
static mut SEM_BEFORE:[QM31;29]=[QM31::ZERO;29];
static mut INACTIVE:E=E::ZERO;
static mut SEM_PTR:*const ()=core::ptr::null();
static mut G_PTR:*const [E;29]=core::ptr::null();
static mut Y1_PTR:*const u8=core::ptr::null();
static mut ROUND0_PTR:*const u8=core::ptr::null();
static mut FINAL_PTR:*const u8=core::ptr::null();
static mut FOLDED:[u8;32]=[0;32];
static mut ROUND1:[u8;224]=[0;224];
fn same_bytes(a:&[u8],b:&[u8]){assert!(a.len()==b.len());let mut i=0;while i<a.len(){assert!(a[i]==b[i]);i+=1;}}
fn same_e(a:E,b:E){let a=a.to_limbs();let b=b.to_limbs();let mut i=0;while i<8{assert!(a[i]==b[i]);i+=1;}}
fn same_q(a:QM31,b:QM31){assert!(a.c0.a==b.c0.a);assert!(a.c0.b==b.c0.b);assert!(a.c1.a==b.c1.a);assert!(a.c1.b==b.c1.b);}
fn same_powers(a:&[E;29],b:&[E;29]){let mut i=0;while i<29{same_e(a[i],b[i]);i+=1;}}

// Exact digest preimages are checked in actual execution order, including all
// eight query squeeze/advance pairs before a sampler error can be returned.
unsafe fn digest_step(parts:&[&[u8]])->[u8;32]{
 let n=DIGEST_CALLS;assert!(n<33);
 if n==0{
  assert!(STAGE==0);assert!(parts.len()==3);
  same_bytes(parts[0],b"UNPROVED:R1:PRIVATE-SALTED:P3");
  same_bytes(parts[1],&[2]);same_bytes(parts[2],&SEM_STATE);STAGE=1;
 }else if n<13{
  let row=(n-1)/3;let step=(n-1)%3;assert!(STAGE==row+1);
  let base=1+3*row;
  if step==0{
   assert!(parts.len()==4);same_bytes(parts[0],&HASHES[base-1]);
   same_bytes(parts[1],&[0,0xa0+27+row as u8]);
   let len=match row{0=>928u32,1=>32,2=>224,_=>256};
   same_bytes(parts[2],&len.to_le_bytes());assert!(parts[3].len()==len as usize);
   match row{
    0=>assert!(parts[3].as_ptr()==Y1_PTR),
    1=>same_bytes(parts[3],&INACTIVE.to_le_bytes()),
    2=>assert!(parts[3].as_ptr()==ROUND0_PTR),
    _=>{same_bytes(&parts[3][..32],&FOLDED);same_bytes(&parts[3][32..],&ROUND1);}
   }
  }else{
   assert!(parts.len()==2);same_bytes(parts[0],&HASHES[base]);
   same_bytes(parts[1],&[step as u8]);
  }
 }else if n<30{
  assert!(STAGE==5);
  if n==13{
   assert!(parts.len()==4);same_bytes(parts[0],&HASHES[12]);
   same_bytes(parts[1],&[0,0xa0+31]);same_bytes(parts[2],&2048u32.to_le_bytes());
   assert!(parts[3].len()==2048);assert!(parts[3].as_ptr()==FINAL_PTR);
  }else{
   let k=(n-14)/2;let step=(n-14)%2;
   assert!(parts.len()==2);same_bytes(parts[0],&HASHES[13+2*k]);
   same_bytes(parts[1],&[1+step as u8]);
  }
 }else{
  assert!(STAGE==6);let step=n-30;
  if step==0{
   assert!(parts.len()==4);same_bytes(parts[0],&STATES[5]);
   same_bytes(parts[1],&[0,0xa0+32]);same_bytes(parts[2],&0u32.to_le_bytes());
   assert!(parts[3].is_empty());
  }else{
   assert!(parts.len()==2);same_bytes(parts[0],&HASHES[30]);
   same_bytes(parts[1],&[step as u8]);
  }
 }
 DIGEST_CALLS=n+1;HASHES[n]
}
fn gamma_stub(block:&[u8;32])->E{unsafe{
 assert!(STAGE==1);assert!(DIGEST_CALLS==4);same_bytes(block,&HASHES[2]);
 let actual=crate::sampler_native::gamma_sample(block);SCALARS[0]=actual;canonical_e(actual);assert!(actual.to_limbs().iter().any(|&x|x!=0));STAGE=2;actual
}}
fn ordinary_stub(block:&[u8;32])->E{unsafe{
 let n=STAGE;assert!(n>=2&&n<=4);assert!(DIGEST_CALLS==1+3*n);
 same_bytes(block,&HASHES[3*n-1]);let actual=crate::sampler_native::ordinary_sample(block);SCALARS[n-1]=actual;canonical_e(actual);STAGE=n+1;actual
}}
fn qm_stub(block:&[u8;32])->QM31{unsafe{
 assert!(STAGE==6);assert!(DIGEST_CALLS==33);same_bytes(block,&HASHES[31]);
 let actual=crate::sampler_native::qm31_sample(block);RHO=actual;canonical_q(actual);STAGE=7;actual
}}
fn pairs_stub(blocks:&[[u8;32];8],advances:&[[u8;32];8])
 ->Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>{unsafe{
 assert!(STAGE==5);assert!(DIGEST_CALLS==30);
 let mut k=0;while k<8{
  same_bytes(&blocks[k],&HASHES[14+2*k]);same_bytes(&advances[k],&HASHES[15+2*k]);k+=1;
 }
 let actual=aspis_core::r0_transcript::s126_queries_from_pairs(blocks,advances);
 match actual{Ok((q,next))=>{QUERY=q;STATES[5]=next;},Err(_)=>{FAIL_AT=0;}}
 STAGE=6;actual
}}
// Only a primitive multiplication normal-return boundary remains here.
// The complete frozen weights::powers body actually executes in Prepared::new.
fn mul_stub(left:E,right:E)->E{unsafe{
 let n=MUL_CALLS;
 let out=if n<28{
  assert!(STAGE==7);same_e(left,POWERS[n]);same_e(right,SCALARS[0]);
  if n==27{STAGE=8;}POWERS[n+1]
 }else if n<34{
  assert!(STAGE==8);let k=n-28;same_e(left,KG[k]);same_e(right,SCALARS[1]);
  if n==33{STAGE=9;}KG[k+1]
 }else{
  assert!(STAGE==10);assert!(n<41);let k=n-34;assert!(CADD==k);
  same_e(left,KG[k]);same_e(right,if k==0{INACTIVE}else{DOT_RET[k-1]});MULTS[k]
 };
 MUL_CALLS=n+1;out
}}
fn same_dot(dot:&crate::fast_pairing::EbyKDot,n:usize){unsafe{
 let (words,count)=dot.proof_words();let mut i=0;
 while i<8{assert!(words[i]==if n%29==0{0}else{DOT_LAST[i]});i+=1;}
 assert!(count==if n%29==0{0}else{DOT_COUNT_LAST});
}}
fn push_stub(dot:&mut crate::fast_pairing::EbyKDot,value:E,scalar:QM31)->Result<(),()>{unsafe{
 assert!(STAGE==9);assert!(MUL_CALLS==34);let n=CPUSH;assert!(n<174);
 let p=n/29;let l=n%29;assert!(CFINISH==p);assert!(CADD==0);
 assert!(CFIELD==if p==5{l+1}else{0});same_dot(dot,n);same_e(value,POWERS[l]);
 same_q(scalar,match p{0..=2=>SEM_CLAIMS[p][l],3=>SEM_EXTRA[l],4=>SEM_BEFORE[l],_=>FIELDS[l].c0()});
 let words=kani::any::<[u64;8]>();let count=kani::any::<usize>();*dot=crate::fast_pairing::EbyKDot::proof_input(words,count);DOT_LAST=words;DOT_COUNT_LAST=count;CPUSH=n+1;
 if n==STOP{Err(())}else{Ok(())}
}}
fn finish_stub(dot:crate::fast_pairing::EbyKDot)->E{unsafe{
 assert!(STAGE==9);assert!(MUL_CALLS==34);assert!(CADD==0);let p=CFINISH;assert!(p<6);
 assert!(CPUSH==29*(p+1));assert!(CFIELD==if p==5{29}else{0});
 let (words,count)=dot.proof_words();let mut i=0;
 while i<8{assert!(words[i]==DOT_LAST[i]);i+=1;}
 assert!(count==DOT_COUNT_LAST);CFINISH=p+1;
 if p==5{STAGE=10;}DOT_RET[p]
}}
fn field_stub(bytes:&[u8],index:usize)->E{unsafe{
 assert!(STAGE==9);assert!(MUL_CALLS==34);assert!(CFINISH==5);assert!(CADD==0);
 assert!(bytes.as_ptr()==Y1_PTR);assert!(bytes.len()==928);assert!(index==CFIELD);
 assert!(index<29);assert!(CPUSH==145+index);CFIELD=index+1;let actual=native_field(bytes,index);same_e(actual,FIELDS[index]);actual
}}
fn add_stub(left:E,right:E)->E{unsafe{
 assert!(STAGE==10);let k=CADD;assert!(k<7);assert!(MUL_CALLS==35+k);
 assert!(CPUSH==174);assert!(CFINISH==6);assert!(CFIELD==29);
 same_e(left,if k==0{E::ZERO}else{ADDS[k-1]});same_e(right,MULTS[k]);CADD=k+1;
 if k==6{STAGE=12;}ADDS[k]
}}
fn any_q()->QM31{QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_row()->[QM31;29]{let mut row=[QM31::ZERO;29];let mut i=0;while i<29{row[i]=any_q();i+=1;}row}
fn any_challenges()->crate::r1_wire::Challenges{let mut zc=[QM31::ZERO;10];let mut i=0;while i<10{zc[i]=any_q();i+=1;}crate::r1_wire::Challenges{lambda:any_q(),chi:any_q(),theta:any_q(),zc,mu:any_q(),eta:any_q()}}
fn any_e()->E{let mut words=[0u32;8];let mut i=0;while i<8{let x=kani::any::<u32>()&0x7fff_ffff;words[i]=if x==0x7fff_ffff{0}else{x};i+=1;}match E::from_limbs(words){Some(e)=>e,None=>{assert!(false);E::ZERO}}}
fn any_es<const N:usize>()->[E;N]{let mut out=[E::ZERO;N];let mut i=0;while i<N{out[i]=any_e();i+=1;}out}
fn any_error()->Error{match kani::any::<u8>()%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}

fn run_case<const POINT:usize>(){
 let mut alpha=[QM31::ZERO;10];let mut i=0;while i<10{alpha[i]=any_q();i+=1;}
 let roots=kani::any::<[[u8;32];2]>();
 let z=[SecureCirclePoint{x:any_q(),y:any_q()},SecureCirclePoint{x:any_q(),y:any_q()}];
 let semantic_state=kani::any::<[u8;32]>();
 let sem=Verified{roots,challenges:any_challenges(),
  alpha,claims:Box::new([any_row(),any_row(),any_row()]),extra:any_row(),before_z1:any_row(),state_before_z0:kani::any(),z,
  transcript:crate::r1_wire::SemanticTranscript::proof_input(Hash,semantic_state,kani::any())};
 let mut y1=[0u8;928];let round0=kani::any::<[u8;224]>();let round1=kani::any::<[u8;224]>();let folded=kani::any::<[u8;32]>();let final_message=kani::any::<[u8;2048]>();
 let inactive=any_e();
 let mut scratch=any_es::<29>();let initial=scratch;
 let scalars=[E::ZERO;4];let mut powers=any_es::<29>();powers[0]=E::ONE;let mut kg=any_es::<7>();kg[0]=E::ONE;let dots=any_es::<6>();let fields=any_es::<29>();let mults=any_es::<7>();let adds=any_es::<7>();let claim=adds[6];let rho=QM31::ZERO;let queries=kani::any::<[u32;22]>();let hashes=kani::any::<[[u8;32];33]>();let selected=(kani::any::<u8>()%8) as usize;let states=[hashes[0],hashes[3],hashes[6],hashes[9],hashes[12],hashes[15+2*selected],hashes[32]];let stop=if POINT<6{29*POINT+(kani::any::<u8>()%29)as usize}else{174};let fail_at=if stop<174{1}else{2};let error=any_error();
 let mut col=0;while col<29{let words=fields[col].to_limbs();let mut j=0;while j<8{let mut b=0;while b<4{y1[32*col+4*j+b]=(words[j]>>(8*b))as u8;b+=1;}j+=1;}col+=1;}

 let view=View{variant:Variant::S2,semantic:&[],y1:&y1,inactive,round0:&round0,folded_root:Some(&folded),round1:&round1,final_message:&final_message,query_bytes:&[]};
 unsafe{SEM_CLAIMS=*sem.claims;SEM_EXTRA=sem.extra;SEM_BEFORE=sem.before_z1;STOP=stop;CPUSH=0;CFINISH=0;CFIELD=0;CADD=0;KG=kg;DOT_RET=dots;FIELDS=fields;MULTS=mults;ADDS=adds;DOT_LAST=[0;8];DOT_COUNT_LAST=0;DIGEST_CALLS=0;HASHES=hashes;STAGE=0;MUL_CALLS=0;FAIL_AT=fail_at;ERROR=error;STATES=states;SEM_STATE=semantic_state;SCALARS=scalars;POWERS=powers;QUERY=queries;RHO=rho;CLAIM=claim;INACTIVE=inactive;
  SEM_PTR=&sem as *const Verified<Hash> as *const ();G_PTR=&scratch;Y1_PTR=y1.as_ptr();ROUND0_PTR=round0.as_ptr();FINAL_PTR=final_message.as_ptr();FOLDED=folded;ROUND1=round1;}
 let tape=kani::any::<[aspis_core::r0_transcript::S126Reply;8]>();
 let mut t=0;while t<8{kani::assume(tape[t].1<=22);kani::assume(tape[t].2<=64);t+=1;}
 // Observer coordinates inspect ghosts only; they do not select replies.
 aspis_core::r0_transcript::s126_init(tape,0,0,0);
 let result=Prepared::new(&sem,&view,Hash,&mut scratch);
 let fail_at=unsafe{FAIL_AT};
 assert!(unsafe{DIGEST_CALLS}==if fail_at==0{30}else{33});
 if fail_at==0{same_powers(&scratch,&initial);assert!(unsafe{STAGE}==6);assert!(unsafe{MUL_CALLS}==0);}else{same_powers(&scratch,&powers);assert!(unsafe{STAGE}==if stop<174{9}else{12});assert!(unsafe{MUL_CALLS}==if stop<174{34}else{41});}
 match result{
  Err(actual)=>{assert!(fail_at<2);assert!(actual==if fail_at==0{Error::Transcript}else{Error::Parse});}
  Ok(out)=>{assert!(fail_at==2);assert!(out.variant==Variant::S2);let mut p=0;while p<2{same_bytes(&out.roots[p],&roots[p]);same_q(out.z[p].x,z[p].x);same_q(out.z[p].y,z[p].y);p+=1;}
   same_e(out.gamma,unsafe{SCALARS[0]});same_e(out.kappa,unsafe{SCALARS[1]});same_e(out.alpha[0],unsafe{SCALARS[2]});same_e(out.alpha[1],unsafe{SCALARS[3]});same_q(out.rho,unsafe{RHO});same_e(out.claim,claim);same_bytes(&out.state,&states[6]);
   i=0;while i<22{assert!(out.queries[i]==unsafe{QUERY[i]});i+=1;}i=0;while i<10{same_q(out.semantic_alpha[i],alpha[i]);i+=1;}
  }
 }
 kani::cover!(fail_at==0,"query error preserves incoming scratch");
 if POINT<6{kani::cover!(fail_at==1,"actual claim push error preserves completed gamma scratch");}
 if fail_at==0{assert!(unsafe{CPUSH}==0);assert!(unsafe{CFINISH}==0);assert!(unsafe{CFIELD}==0);assert!(unsafe{CADD}==0);}
 else if stop<174{assert!(unsafe{CPUSH}==stop+1);assert!(unsafe{CFINISH}==stop/29);assert!(unsafe{CFIELD}==if stop<145{0}else{stop-145+1});assert!(unsafe{CADD}==0);}
 else{assert!(unsafe{CPUSH}==174);assert!(unsafe{CFINISH}==6);assert!(unsafe{CFIELD}==29);assert!(unsafe{CADD}==7);}
 if POINT==6{kani::cover!(fail_at==2,"complete native Prepared return and original claim aggregation");}
}

#[kani::proof]
#[kani::unwind(257)]
#[kani::stub(crate::sampler::gamma_sample,gamma_stub)]
#[kani::stub(crate::sampler::ordinary_sample,ordinary_stub)]
#[kani::stub(crate::sampler::qm31_sample,qm_stub)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]
#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn prepared_new_claim_point_0(){run_case::<0>();}
#[kani::proof]
#[kani::unwind(257)]
#[kani::stub(crate::sampler::gamma_sample,gamma_stub)]
#[kani::stub(crate::sampler::ordinary_sample,ordinary_stub)]
#[kani::stub(crate::sampler::qm31_sample,qm_stub)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]
#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn prepared_new_claim_point_1(){run_case::<1>();}
#[kani::proof]
#[kani::unwind(257)]
#[kani::stub(crate::sampler::gamma_sample,gamma_stub)]
#[kani::stub(crate::sampler::ordinary_sample,ordinary_stub)]
#[kani::stub(crate::sampler::qm31_sample,qm_stub)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]
#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn prepared_new_claim_point_2(){run_case::<2>();}
#[kani::proof]
#[kani::unwind(257)]
#[kani::stub(crate::sampler::gamma_sample,gamma_stub)]
#[kani::stub(crate::sampler::ordinary_sample,ordinary_stub)]
#[kani::stub(crate::sampler::qm31_sample,qm_stub)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]
#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn prepared_new_claim_point_3(){run_case::<3>();}
#[kani::proof]
#[kani::unwind(257)]
#[kani::stub(crate::sampler::gamma_sample,gamma_stub)]
#[kani::stub(crate::sampler::ordinary_sample,ordinary_stub)]
#[kani::stub(crate::sampler::qm31_sample,qm_stub)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]
#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn prepared_new_claim_point_4(){run_case::<4>();}
#[kani::proof]
#[kani::unwind(257)]
#[kani::stub(crate::sampler::gamma_sample,gamma_stub)]
#[kani::stub(crate::sampler::ordinary_sample,ordinary_stub)]
#[kani::stub(crate::sampler::qm31_sample,qm_stub)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]
#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn prepared_new_claim_point_5(){run_case::<5>();}
#[kani::proof]
#[kani::unwind(257)]
#[kani::stub(crate::sampler::gamma_sample,gamma_stub)]
#[kani::stub(crate::sampler::ordinary_sample,ordinary_stub)]
#[kani::stub(crate::sampler::qm31_sample,qm_stub)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]
#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn prepared_new_claim_point_6(){run_case::<6>();}

fn native_field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }

fn canonical_e(x:E){let limbs=x.to_limbs();let mut j=0;while j<8{assert!(limbs[j]<aspis_core::field::P);j+=1;}}
fn canonical_q(x:QM31){assert!(x.c0.a.0<aspis_core::field::P);assert!(x.c0.b.0<aspis_core::field::P);assert!(x.c1.a.0<aspis_core::field::P);assert!(x.c1.b.0<aspis_core::field::P);}
