use super::*;
#[derive(Clone,Copy)] struct NBR_Digest;
static mut NBR_ENABLED:bool=false;
impl Digest32 for NBR_Digest{fn digest(&self,_:&[&[u8]])->[u8;32]{unsafe{assert!(!NBR_ENABLED,"no digest after returned claim");}kani::any()}}
fn NBR_claim_tail<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,t:Transcript<H>,gamma:E,kappa:E,alpha:[E;2],rho:K,queries:[u32;22],returned:Result<E,Error>)->Result<Box<Prepared>,Error>{
 let claim=returned?;
 Ok(Box::new(Prepared{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
}
#[kani::proof] #[kani::unwind(33)]
fn NBR_claim_tail_all_fields(){
 let q=K::ZERO;unsafe{NBR_ENABLED=false;}
 let sem=crate::r1_semantic::Verified{roots:kani::any(),challenges:crate::r1_wire::Challenges{lambda:q,chi:q,theta:q,zc:[q;10],mu:q,eta:q},alpha:unsafe{core::mem::transmute::<[u8;160],[K;10]>(kani::any())},claims:Box::new([[q;29];3]),extra:[q;29],before_z1:[q;29],state_before_z0:kani::any(),z:unsafe{core::mem::transmute::<[u8;64],[SecureCirclePoint;2]>(kani::any())},transcript:crate::r1_wire::SemanticTranscript::new(NBR_Digest,&[],&kani::any()).unwrap()};
 let v=View{variant:Variant::S2,semantic:&[],y1:&[],inactive:E::ZERO,round0:&[],folded_root:None,round1:&[],final_message:&[],query_bytes:&[]};
 let mut t=Transcript::new(NBR_Digest,kani::any(),Variant::S2);t.state=kani::any();let state=t.state;
 let gamma:E=unsafe{core::mem::transmute::<[u8;32],E>(kani::any())};let kappa:E=unsafe{core::mem::transmute::<[u8;32],E>(kani::any())};let alpha:[E;2]=unsafe{core::mem::transmute::<[u8;64],[E;2]>(kani::any())};let rho:K=unsafe{core::mem::transmute::<[u8;16],K>(kani::any())};let queries:[u32;22]=kani::any();let claim:E=unsafe{core::mem::transmute::<[u8;32],E>(kani::any())};
 let choice:u8=kani::any();kani::assume(choice<=8);let error=match choice{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation};let returned=if choice==8{Ok(claim)}else{Err(error)};
 unsafe{NBR_ENABLED=true;}
 let i:usize=kani::any();let b:usize=kani::any();let j:usize=kani::any();let a:usize=kani::any();kani::assume(i<32&&b<2&&j<22&&a<10);
 let r=NBR_claim_tail(&sem,&v,t,gamma,kappa,alpha,rho,queries,returned);
 if choice==8{let p=r.unwrap();assert_eq!(p.variant,Variant::S2);assert_eq!(p.roots[b][i],sem.roots[b][i]);assert_eq!(p.gamma,gamma);assert_eq!(p.kappa,kappa);assert_eq!(p.alpha[b],alpha[b]);assert_eq!(p.rho,rho);assert_eq!(p.queries[j],queries[j]);assert_eq!(p.semantic_alpha[a],sem.alpha[a]);assert_eq!(p.z[b],sem.z[b]);assert_eq!(p.claim,claim);assert_eq!(p.state[i],state[i]);kani::cover!(true,"complete Prepared uses SAME returned native carriers");}else{match r{Err(e)=>assert_eq!(e,error),Ok(_)=>assert!(false,"error was swallowed")};kani::cover!(true,"all eight returned error variants propagate without a suffix");}
}
