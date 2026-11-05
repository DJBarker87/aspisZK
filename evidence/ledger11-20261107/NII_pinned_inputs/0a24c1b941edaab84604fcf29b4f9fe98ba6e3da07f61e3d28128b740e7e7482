use super::*;
use aspis_core::field::CM31;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]struct Hash(u8);
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{assert!(false,"unexpected digest outside oracle cut");[0;32]}}
fn any_q()->K{K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_e()->E{let words:[u32;8]=kani::any();let mut i=0;while i<8{kani::assume(words[i]<2147483647);i+=1;}E::from_limbs(words).unwrap()}
fn es<const N:usize>()->[E;N]{let mut xs=[E::ZERO;N];let mut i=0;while i<N{xs[i]=any_e();i+=1;}xs}
fn qs<const N:usize>()->[K;N]{let mut xs=[K::ZERO;N];let mut i=0;while i<N{xs[i]=any_q();i+=1;}xs}
fn error(code:u8)->Error{match code%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn semantic(hash:Hash)->crate::r1_semantic::Verified<Hash>{
 let c=crate::r1_wire::Challenges{lambda:any_q(),chi:any_q(),theta:any_q(),zc:qs(),mu:any_q(),eta:any_q()};
 crate::r1_semantic::Verified{roots:kani::any(),challenges:c,alpha:qs(),claims:Box::new([qs(),qs(),qs()]),extra:qs(),before_z1:qs(),state_before_z0:kani::any(),z:[SecureCirclePoint{x:any_q(),y:any_q()},SecureCirclePoint{x:any_q(),y:any_q()}],transcript:crate::r1_wire::NFW_wire::seed(hash,kani::any(),kani::any())}
}
struct Ops {output_facet:usize,output_word:usize,output_index:usize,empty_audit:bool,payload_audit:bool,expected:[u8;6],audit:bool,audit_word:usize,states:[[u8;32];7],scalars:[E;4],rho:K,queries:[u32;22],powers:[E;29],claim:E,q_error:bool,c_error:bool,error:Error,
 calls:usize,sc:usize,rows:[u8;6],lens:[usize;6],ptrs:[usize;6],samples:[u8;6],positions:[usize;6],before:[[u8;32];7],before_hash:[u8;6],nonzero:[bool;4],hash:u8,variant:u8,seed:[u8;32],gamma:E,claim_sem:usize,claim_y1:usize,claim_len:usize,claim_inactive:E,claim_kappa:E,claim_g:E,slot:usize}
struct OracleTranscript<'a>{state:[u8;32],hash:Hash,ops:&'a mut Ops}
impl<'a> OracleTranscript<'a>{
 fn new(hash:Hash,seed:[u8;32],variant:Variant,ops:&'a mut Ops)->Self{ops.calls+=1;ops.hash=hash.0;ops.seed=seed;ops.variant=match variant{Variant::S1=>1,Variant::S2=>2,Variant::D=>3};Self{state:ops.states[0],hash,ops}}
 fn record(&mut self,i:usize,row:u8,payload:&[u8]){let target=if cfg!(NFW_call0){0}else if cfg!(NFW_call1){1}else if cfg!(NFW_call2){2}else if cfg!(NFW_call3){3}else if cfg!(NFW_call4){4}else{5};if self.ops.audit&&i==target{let w=self.ops.audit_word;assert!((self.state[w]==self.ops.states[i][w]&&self.hash.0==self.ops.hash)!=cfg!(NFW_invert));kani::assume(false);}if self.ops.payload_audit&&i==target{let at=self.ops.positions[i];let value=if at<payload.len(){payload[at]}else{0};assert!((row==[27,28,29,30,31,32][i]&&payload.len()==[928,32,224,256,2048,0][i]&&value==self.ops.expected[i]&&(i>=4||self.ops.nonzero[i]==(i==0)))!=cfg!(NFW_invert));kani::assume(false);}self.ops.calls+=1;self.ops.rows[i]=row;self.ops.lens[i]=payload.len();self.ops.ptrs[i]=payload.as_ptr() as usize;let at=self.ops.positions[i];self.ops.samples[i]=if at<payload.len(){payload[at]}else{0};self.ops.before[i]=self.state;self.ops.before_hash[i]=self.hash.0;}
 fn scalar(&mut self,row:u8,payload:&[u8],nonzero:bool)->E{let i=self.ops.sc;self.ops.nonzero[i]=nonzero;self.record(i,row,payload);self.ops.sc+=1;self.state=self.ops.states[i+1];self.ops.scalars[i]}
 fn queries(&mut self,row:u8,payload:&[u8])->Result<[u32;22],Error>{self.record(4,row,payload);self.state=self.ops.states[5];if self.ops.q_error{Err(self.ops.error)}else{Ok(self.ops.queries)}}
 fn scalar_k(&mut self,row:u8,payload:&[u8])->K{if self.ops.empty_audit{assert!((row==32&&payload.is_empty())!=cfg!(NFW_invert));kani::assume(false);}self.record(5,row,payload);self.state=self.ops.states[6];self.ops.rho}
}
fn power(gamma:E,ops:&mut Ops)->[E;29]{ops.calls+=1;ops.gamma=gamma;ops.powers}
fn claim(sem:&crate::r1_semantic::Verified<Hash>,y1:&[u8],inactive:E,g:&[E;29],kappa:E,ops:&mut Ops)->Result<E,Error>{ops.calls+=1;ops.claim_sem=sem as *const _ as usize;ops.claim_y1=y1.as_ptr() as usize;ops.claim_len=y1.len();ops.claim_inactive=inactive;ops.claim_kappa=kappa;ops.claim_g=g[ops.slot];if ops.c_error{Err(ops.error)}else{Ok(ops.claim)}}
fn new(sem:&crate::r1_semantic::Verified<Hash>,v:&View<'_>,hash:Hash,g:&mut[E;29],ops:&mut Ops)->Result<Box<Prepared>,Error>{

        let mut t=OracleTranscript::new(hash,sem.transcript.state(),v.variant,ops);
        let gamma=t.scalar(27,v.y1,true);
        let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);
        let alpha0=t.scalar(29,v.round0,false);
        let (alpha,row)=if v.variant.folds()==2 {
            let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
            ([alpha0,t.scalar(30,&bytes,false)],31)
        } else {
            ([alpha0,E::ZERO],30)
        };
        let queries=t.queries(row,v.final_message)?;
        let rho=t.scalar_k(row+1,&[]);
        // Reuse this caller-owned scratch array in tx1; it is never serialized.
        *g=power(gamma,t.ops);
        let claim=claim(sem,v.y1,v.inactive,g,kappa,t.ops)?;
        let value=Prepared{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state};let value=capture_prepared(value,sem,t.ops);Ok(Box::new(value))
    
}
fn ops(slot:usize)->Ops{Ops{output_facet:5,output_word:0,output_index:0,empty_audit:false,payload_audit:false,expected:[0;6],audit:false,audit_word:0,states:kani::any(),scalars:es(),rho:any_q(),queries:kani::any(),powers:es(),claim:any_e(),q_error:kani::any(),c_error:kani::any(),error:error(kani::any()),calls:0,sc:0,rows:[0;6],lens:[0;6],ptrs:[0;6],samples:[0;6],positions:kani::any(),before:[[0;32];7],before_hash:[0;6],nonzero:[false;4],hash:0,variant:0,seed:[0;32],gamma:E::ZERO,claim_sem:0,claim_y1:0,claim_len:0,claim_inactive:E::ZERO,claim_kappa:E::ZERO,claim_g:E::ZERO,slot}}
fn check(facet:usize){if cfg!(NFW_RETURN_BLOCK){return_block_check();return;}
 let hash=Hash(kani::any());let sem=semantic(hash);let semantic:[u8;13831]=kani::any();let y1:[u8;928]=kani::any();let round0:[u8;224]=kani::any();let root:[u8;32]=kani::any();let round1:[u8;224]=kani::any();let final_message:[u8;2048]=kani::any();
 let v=View{variant:Variant::S2,semantic:&semantic,y1:&y1,inactive:any_e(),round0:&round0,folded_root:Some(&root),round1:&round1,final_message:&final_message,query_bytes:&[]};
 let slot:usize=kani::any();let word:usize=kani::any();kani::assume(slot<29&&word<8);let mut g=es::<29>();let old=g[slot].to_limbs()[word];let mut o=ops(slot);o.output_facet=if cfg!(NFW_CAPTURE_ALL){let f:usize=kani::any();kani::assume(f>=5&&f<=15);f}else{facet};o.output_word=word;o.output_index=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(o.output_index<match o.output_facet{7|12=>2,8=>22,10=>64,11=>10,13=>32,_=>1});if cfg!(NFW_invert){o.positions=[0;6];}o.audit=facet==16;o.empty_audit=facet==17&&cfg!(NFW_EMPTY_RHO);o.payload_audit=facet==17&&!cfg!(NFW_EMPTY_RHO);if facet==17&&!cfg!(NFW_EMPTY_RHO){let mut ei=0;while ei<6{let at=o.positions[ei];o.expected[ei]=match ei{0=>if at<928{y1[at]}else{0},1=>if at<32{v.inactive.to_le_bytes()[at]}else{0},2=>if at<224{round0[at]}else{0},3=>if at<32{root[at]}else if at<256{round1[at-32]}else{0},4=>if at<2048{final_message[at]}else{0},_=>0};ei+=1;}}o.audit_word=kani::any();kani::assume(o.audit_word<32);if cfg!(NFW_invert){kani::assume(o.q_error==(facet<5 && facet!=1 && facet!=2 && !(facet==3 && cfg!(NFW_call5)))&& !o.c_error&&word==0&&slot==0);}let result=new(&sem,&v,hash,&mut g,&mut o);
 let good=if o.q_error {matches!(result,Err(e) if e==o.error)&&g[slot].to_limbs()[word]==old&&o.calls==6}
 else if o.c_error {matches!(result,Err(e) if e==o.error)&&g[slot].to_limbs()[word]==o.powers[slot].to_limbs()[word]&&o.calls==9}
 else {result.is_ok()&&o.calls==9};
 if facet==16||facet==17||cfg!(NFW_CAPTURE_FIELDS){return;}if facet==0{assert!(good!=cfg!(NFW_invert));return;}
 if facet==1{if o.q_error{return;}}
 if facet==2{if o.q_error{return;}}
 if facet==1{assert!((o.gamma.to_limbs()[word]==o.scalars[0].to_limbs()[word])!=cfg!(NFW_invert));return;}
 if facet==2{assert!((o.claim_sem==&sem as *const _ as usize&&o.claim_y1==y1.as_ptr() as usize&&o.claim_len==928&&o.claim_inactive.to_limbs()[word]==v.inactive.to_limbs()[word]&&o.claim_kappa.to_limbs()[word]==o.scalars[1].to_limbs()[word]&&o.claim_g.to_limbs()[word]==o.powers[slot].to_limbs()[word])!=cfg!(NFW_invert));return;}
 if facet==3{
  let w:usize=kani::any();kani::assume(w<32);let i=if cfg!(NFW_call0){0}else if cfg!(NFW_call1){1}else if cfg!(NFW_call2){2}else if cfg!(NFW_call3){3}else if cfg!(NFW_call4){4}else{5};kani::assume(i<if o.q_error{5}else{6});
  let seed_ok=o.seed[w]==sem.transcript.state()[w]&&o.hash==hash.0&&o.variant==2;
  let chain=o.before[i][w]==o.states[i][w]&&o.before_hash[i]==hash.0;assert!((seed_ok&&chain)!=cfg!(NFW_invert));return;
 }
 if facet==4{
  let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<if o.q_error{5}else{6});let at=o.positions[i];let expected=match i{0=>if at<928{y1[at]}else{0},1=>if at<32{v.inactive.to_le_bytes()[at]}else{0},2=>if at<224{round0[at]}else{0},3=>if at<32{root[at]}else if at<256{round1[at-32]}else{0},4=>if at<2048{final_message[at]}else{0},_=>0};
  assert!((o.samples[i]==expected&&o.rows[i]==[27,28,29,30,31,32][i]&&o.lens[i]==[928,32,224,256,2048,0][i]&&(if i<4{o.nonzero[i]==(i==0)}else{true}))!=cfg!(NFW_invert));return;
 }
 if o.q_error||o.c_error{return;}let p=result.unwrap();
 let value=match facet{5=>p.gamma.to_limbs()[word]==o.scalars[0].to_limbs()[word],6=>p.kappa.to_limbs()[word]==o.scalars[1].to_limbs()[word],7=>{let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<2);p.alpha[i].to_limbs()[word]==o.scalars[i+2].to_limbs()[word]},8=>{let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<22);p.queries[i]==o.queries[i]},9=>p.claim.to_limbs()[word]==o.claim.to_limbs()[word],10=>{let i:usize=if cfg!(NFW_invert){0}else{kani::any()};let j:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<2&&j<32);p.roots[i][j]==sem.roots[i][j]},11=>{let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<10);p.semantic_alpha[i]==sem.alpha[i]},12=>{let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<2);p.z[i]==sem.z[i]},13=>{let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<32);p.state[i]==o.states[6][i]},14=>p.rho==o.rho,_=>p.variant==Variant::S2};
 assert!(value!=cfg!(NFW_invert));
}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet0(){check(0);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet1(){check(1);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet2(){check(2);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet3(){check(3);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet4(){check(4);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet5(){check(5);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet6(){check(6);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet7(){check(7);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet8(){check(8);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet9(){check(9);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet10(){check(10);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet11(){check(11);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet12(){check(12);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet13(){check(13);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet14(){check(14);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet15(){check(15);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet16(){check(16);}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet17(){check(17);}

#[kani::proof] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_q(){let src=qs::<10>();let mut dst=[K::ZERO;10];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),10);}let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<10);assert!((src[i]==dst[i])!=cfg!(NFW_invert));}
#[kani::proof] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_point(){let src=[SecureCirclePoint{x:any_q(),y:any_q()},SecureCirclePoint{x:any_q(),y:any_q()}];let mut dst=[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),2);}let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<2);assert!((src[i]==dst[i])!=cfg!(NFW_invert));}
#[kani::proof] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_queries(){let src:[u32;22]=kani::any();let mut dst=[0u32;22];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),22);}let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<22);assert!((src[i]==dst[i])!=cfg!(NFW_invert));}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn copy_folded_wrong(){let mut root=[0u8;32];root[31]=17;let mut tail=[0u8;224];tail[223]=128;let mut dst=Vec::with_capacity(256);dst.extend_from_slice(&root);dst.extend_from_slice(&tail);assert_eq!(dst[255],0);}

#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn copy_folded(){let root:[u8;32]=kani::any();let tail:[u8;224]=kani::any();let mut dst=Vec::with_capacity(256);dst.extend_from_slice(&root);dst.extend_from_slice(&tail);let at:usize=kani::any();kani::assume(at<256);let expected=if at<32{root[at]}else{tail[at-32]};assert_eq!(dst[at],expected);}

fn capture_prepared(p:Prepared,sem:&crate::r1_semantic::Verified<Hash>,o:&mut Ops)->Prepared{
 if cfg!(NFW_CAPTURE_FIELDS){let word=o.output_word;let i=o.output_index;
 let value=match o.output_facet{
 5=>p.gamma.to_limbs()[word]==o.scalars[0].to_limbs()[word],
 6=>p.kappa.to_limbs()[word]==o.scalars[1].to_limbs()[word],
 7=>p.alpha[i].to_limbs()[word]==o.scalars[i+2].to_limbs()[word],
 8=>p.queries[i]==o.queries[i],9=>p.claim.to_limbs()[word]==o.claim.to_limbs()[word],
 10=>p.roots[i/32][i%32]==sem.roots[i/32][i%32],11=>p.semantic_alpha[i]==sem.alpha[i],
 12=>p.z[i]==sem.z[i],13=>p.state[i]==o.states[6][i],14=>p.rho==o.rho,_=>p.variant==Variant::S2};
 assert!(value!=cfg!(NFW_invert));kani::assume(false);}
 p
}
// Arbitrary valid prestate of the final frozen return expression. No opening
// prefix, field multiplication, scratch-buffer loop, or independent output.
fn return_block_source(sem:&crate::r1_semantic::Verified<Hash>,variant:Variant,gamma:E,kappa:E,alpha:[E;2],rho:K,queries:[u32;22],claim:E,state:[u8;32])->Box<Prepared>{
 Box::new(Prepared{variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state})
}
fn return_block_check(){
 let sem=semantic(Hash(kani::any()));let v:u8=kani::any();let variant=match v%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};let gamma=any_e();let kappa=any_e();let alpha=es::<2>();let rho=any_q();let queries:[u32;22]=kani::any();let claim=any_e();let state:[u8;32]=kani::any();
 let word:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(word<8);let field:usize=if cfg!(NFW_invert){5}else{kani::any()};kani::assume(field>=5&&field<=15);let i:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(i<match field{7|12=>2,8=>22,10=>64,11=>10,13=>32,_=>1});
 let p=return_block_source(&sem,variant,gamma,kappa,alpha,rho,queries,claim,state);
 let good=match field{5=>p.gamma.to_limbs()[word]==gamma.to_limbs()[word],6=>p.kappa.to_limbs()[word]==kappa.to_limbs()[word],7=>p.alpha[i].to_limbs()[word]==alpha[i].to_limbs()[word],8=>p.queries[i]==queries[i],9=>p.claim.to_limbs()[word]==claim.to_limbs()[word],10=>p.roots[i/32][i%32]==sem.roots[i/32][i%32],11=>p.semantic_alpha[i]==sem.alpha[i],12=>p.z[i]==sem.z[i],13=>p.state[i]==state[i],14=>p.rho==rho,_=>p.variant==variant};assert!(good!=cfg!(NFW_invert));
}
