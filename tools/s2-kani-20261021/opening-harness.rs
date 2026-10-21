fn reference<H:Digest32>(sem:&r1_semantic::Verified<H>,v:&View<'_>,hash:H,g:&mut[E;29])->Result<Box<Prepared>,Error>{
let mut t=Transcript::new(hash,sem.transcript.state(),Variant::S2);
let gamma=t.scalar(27,v.y1,true);
let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);
let alpha0=t.scalar(29,v.round0,false);
let mut message=[0u8;256];message[..32].copy_from_slice(v.folded_root.unwrap());message[32..].copy_from_slice(v.round1);
let alpha1=t.scalar(30,&message,false);
let queries=t.queries(31,v.final_message)?;
let rho=t.scalar_k(32,&[]);
*g=powers::<29>(gamma);
let claim=prepared_claim(sem,v.y1,v.inactive,g,kappa)?;
Ok(Box::new(Prepared{variant:Variant::S2,roots:sem.roots,gamma,kappa,alpha:[alpha0,alpha1],rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
}
fn fields(p:&Prepared)->(E,E,[E;2],K,[u32;22],E,[u8;32]){(p.gamma,p.kappa,p.alpha,p.rho,p.queries,p.claim,p.state)}
#[cfg(kani)] mod proofs {use super::*;
#[kani::proof] #[kani::unwind(258)] fn opening_dispatch_bytes(){
let y1:[u8;928]=kani::any();let round0:[u8;224]=kani::any();let root:[u8;32]=kani::any();let round1:[u8;224]=kani::any();let final_message:[u8;2048]=kani::any();
let states:[[u8;32];6]=kani::any();let claim_fail:bool=kani::any();
let inactive:[u8;32]=kani::any();let values:[u32;6]=kani::any();let queries:[u32;22]=kani::any();let fail:bool=kani::any();let probe:usize=kani::any();
unsafe{STATES=states;CLAIM_FAIL=claim_fail;INACTIVE=inactive;VALUES=values;QUERIES=queries;FAIL=fail;PROBE=probe;EVENTS=[EMPTY;6];COUNT=0;}
let sem=r1_semantic::Verified{transcript:Transcript::new(Hash,[0;32],Variant::S2),roots:[[0;32];2],alpha:[0;10],z:[0;2]};
let view=View{variant:Variant::S2,y1:&y1,inactive:E(0),round0:&round0,folded_root:Some(&root),round1:&round1,final_message:&final_message};
let mut g=[E::ZERO;29];let x=Prepared::new(&sem,&view,Hash,&mut g);let trace=unsafe{EVENTS};let count=unsafe{COUNT};
unsafe{EVENTS=[EMPTY;6];COUNT=0;}let mut rg=[E::ZERO;29];let y=reference(&sem,&view,Hash,&mut rg);
assert_eq!(trace,unsafe{EVENTS});assert_eq!(count,unsafe{COUNT});assert_eq!(g,rg);
match (x,y){(Ok(x),Ok(y))=>{assert_eq!(fields(&x),fields(&y));assert_eq!(x.roots,y.roots);assert_eq!(x.semantic_alpha,y.semantic_alpha);assert_eq!(x.z,y.z);assert_eq!(x.variant,y.variant);},(Err(x),Err(y))=>assert_eq!(x,y),_=>assert!(false)}
assert_eq!(count,if fail{5}else{6});
}}
#[cfg(kani)] mod state_proofs {use super::*;
#[kani::proof] #[kani::unwind(258)] fn opening_state_threading(){
let states:[[u8;32];6]=kani::any();let query_fail:bool=kani::any();let claim_fail:bool=kani::any();
unsafe{STATES=states;FAIL=query_fail;CLAIM_FAIL=claim_fail;INACTIVE=[0;32];VALUES=[0;6];QUERIES=[0;22];PROBE=usize::MAX;EVENTS=[EMPTY;6];COUNT=0;}
let y1=[0u8;928];let round0=[0u8;224];let root=[0u8;32];let round1=[0u8;224];let final_message=[0u8;2048];
let sem=r1_semantic::Verified{transcript:Transcript::new(Hash,[0;32],Variant::S2),roots:[[0;32];2],alpha:[0;10],z:[0;2]};
let view=View{variant:Variant::S2,y1:&y1,inactive:E(0),round0:&round0,folded_root:Some(&root),round1:&round1,final_message:&final_message};
let mut g=[E::ZERO;29];let out=Prepared::new(&sem,&view,Hash,&mut g);
let count=unsafe{COUNT};assert_eq!(count,if query_fail{5}else{6});
let i:usize=kani::any();kani::assume(i<count);
let event=unsafe{EVENTS[i]};assert_eq!(event.row,27+i as u8);
assert_eq!(event.before,if i==0{[0;32]}else{states[i-1]});
if query_fail {assert!(matches!(out,Err(Error::Transcript)));}
else if claim_fail {assert!(matches!(out,Err(Error::Relation)));}
else {assert_eq!(out.unwrap().state,states[5]);}
}}
