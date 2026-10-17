//! Native test-only equivalence gate; injected interface failures are synthetic.
use super::*;
use alloc::{vec, vec::Vec, boxed::Box};
use aspis_core::{field::{CM31, M31, QM31 as K}, Digest32};
use sha2::{Digest, Sha256};
use std::cell::RefCell;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct Faults { push_fail: Option<usize>, query_fail: bool, pushes: Vec<([u8;32],[u8;16])>, queries: usize }
std::thread_local! {
    static FAULTS: RefCell<Faults> = RefCell::new(Faults::default());
    static DIGESTS: RefCell<Vec<(Vec<Vec<u8>>,[u8;32])>> = const { RefCell::new(Vec::new()) };
}
pub(crate) fn before_push(value:E, scalar:K)->bool {
    FAULTS.with(|state| {let mut state=state.borrow_mut();let index=state.pushes.len();state.pushes.push((value.to_le_bytes(),kb(scalar)));state.push_fail==Some(index)})
}
pub(crate) fn before_queries()->bool {
    FAULTS.with(|state| {let mut state=state.borrow_mut();state.queries+=1;state.query_fail})
}
#[derive(Clone, Copy)]
struct RecordedSha;
impl Digest32 for RecordedSha {
    fn digest(&self, parts:&[&[u8]])->[u8;32] {
        let mut hash=Sha256::new();for part in parts {hash.update(part);}
        let out:[u8;32]=hash.finalize().into();
        DIGESTS.with(|log|log.borrow_mut().push((parts.iter().map(|x|x.to_vec()).collect(),out)));out
    }
}
fn kb(q:K)->[u8;16] {let mut bytes=[0;16];q.write_le_bytes(&mut bytes);bytes}
fn k(n:u32)->K {K{c0:CM31{a:M31(n),b:M31(n+1)},c1:CM31{a:M31(n+2),b:M31(n+3)}}}
fn e(n:u32)->E {E::new(k(n),k(n+4))}
fn semantic()->crate::r1_semantic::Verified<RecordedSha> {
    crate::r1_semantic::Verified {
        roots:[[7;32],[19;32]],
        challenges:crate::r1_wire::Challenges {lambda:k(1),chi:k(11),theta:k(21),zc:core::array::from_fn(|i|k(31+i as u32*4)),mu:k(81),eta:k(91)},
        alpha:core::array::from_fn(|i|k(101+i as u32*4)),
        claims:Box::new(core::array::from_fn(|p|core::array::from_fn(|l|k(151+p as u32*200+l as u32*4)))),
        extra:core::array::from_fn(|l|k(811+l as u32*4)),before_z1:core::array::from_fn(|l|k(1011+l as u32*4)),
        state_before_z0:[23;32],z:[SecureCirclePoint{x:k(1201),y:k(1211)},SecureCirclePoint{x:k(1221),y:k(1231)}],
        transcript:crate::r1_wire::SemanticTranscript::new(RecordedSha,b"prepared-migration-test",&[7;32]).unwrap(),
        round_checks:[[K::ZERO;3];10],terminal:K::ZERO,masked_terminal:K::ZERO,
    }
}
fn encode(pre:&Prepared)->Vec<u8> {
    let mut out=vec![pre.variant.tag()];for root in pre.roots {out.extend_from_slice(&root);}
    for x in [pre.gamma,pre.kappa,pre.alpha[0],pre.alpha[1]] {out.extend_from_slice(&x.to_le_bytes());}
    out.extend_from_slice(&kb(pre.rho));for x in pre.queries {out.extend_from_slice(&x.to_le_bytes());}
    for x in pre.semantic_alpha {out.extend_from_slice(&kb(x));}
    for z in pre.z {out.extend_from_slice(&kb(z.x));out.extend_from_slice(&kb(z.y));}
    out.extend_from_slice(&pre.claim.to_le_bytes());out.extend_from_slice(&pre.state);out
}
#[derive(Debug,PartialEq,Eq)]
struct Outcome { error:Option<Error>, prepared:Vec<u8>, values:Vec<(u16,usize,[u8;32])>, digests:Vec<(Vec<Vec<u8>>,[u8;32])>, faults:Faults }
fn run(old:bool,variant:Variant,push_fail:Option<usize>,query_fail:bool)->Outcome {
    let sem=semantic();let y1:Vec<u8>=(0..29).flat_map(|i|E::from_qm31(k(1501+i*4)).to_le_bytes()).collect();
    let round0:Vec<u8>=(0..7).flat_map(|i|e(1701+i*8).to_le_bytes()).collect();
    let round1:Vec<u8>=(0..7).flat_map(|i|e(1801+i*8).to_le_bytes()).collect();
    let message:Vec<u8>=(0..variant.final_len()).flat_map(|i|e(2001+i as u32*8).to_le_bytes()).collect();
    let root=[29;32];let view=View{variant,semantic:&[],y1:&y1,inactive:e(1401),round0:&round0,folded_root:if variant.folds()==2{Some(&root)}else{None},round1:if variant.folds()==2{&round1}else{&[]},final_message:&message,query_bytes:&[]};
    FAULTS.with(|s|*s.borrow_mut()=Faults{push_fail,query_fail,..Faults::default()});DIGESTS.with(|s|s.borrow_mut().clear());let _=crate::trace::take();
    let result=if old {Prepared::migration_old_new(&sem,&view,RecordedSha)} else {Prepared::new(&sem,&view,RecordedSha)};
    let (error,prepared)=match result {Ok(pre)=>(None,encode(&pre)),Err(error)=>(Some(error),Vec::new())};
    Outcome{error,prepared,values:crate::trace::take(),digests:DIGESTS.with(|s|core::mem::take(&mut*s.borrow_mut())),faults:FAULTS.with(|s|s.borrow().clone())}
}
fn check(variant:Variant,push_fail:Option<usize>,query_fail:bool) {
    let old=run(true,variant,push_fail,query_fail);let new=run(false,variant,push_fail,query_fail);
    assert_eq!(old,new,"variant={variant:?} push_fail={push_fail:?} query_fail={query_fail}");
    assert_eq!(old.error,if query_fail {Some(Error::Transcript)} else if push_fail.is_some(){Some(Error::Parse)}else{None});
    assert_eq!(old.faults.queries,1);
    assert_eq!(old.faults.pushes.len(),if query_fail {0}else{push_fail.map(|i|i+1).unwrap_or(174)});
    let row=if variant.folds()==1 {30}else{31};
    let expected_rows:Vec<usize>=if query_fail {if variant.folds()==1{vec![27,28,29]}else{vec![27,28,29,30]}}else{if variant.folds()==1{vec![27,28,29,row+1]}else{vec![27,28,29,30,row+1]}};
    assert_eq!(old.values.iter().filter(|(tag,_,_)|*tag==4).map(|(_,i,_)|*i).collect::<Vec<_>>(),expected_rows);
    assert_eq!(old.values.iter().filter(|(tag,_,_)|*tag==5).count(),if query_fail{0}else{22});
    assert_eq!(old.values.iter().filter(|(tag,_,_)|*tag==14).map(|(_,i,_)|*i).collect::<Vec<_>>(),if !query_fail&&push_fail.is_none(){(0..8).collect()}else{Vec::new()});
    std::println!("{}",serde_json::json!({"variant":variant.tag(),"push_failure":push_fail,"query_failure":query_fail,"error":old.error.map(|e|std::format!("{e:?}")),"trace_values":old.values,"digest_calls":old.digests,"pushes":old.faults.pushes,"prepared":old.prepared,"old_new_equal":true}));
}
#[test]
fn prepared_exact_old_new_failures_and_success() {
    for variant in [Variant::S1,Variant::S2,Variant::D] {
        check(variant,None,false);check(variant,None,true);
        for i in 0..174 {check(variant,Some(i),false);}
    }
    std::println!("PREPARED_MIGRATION_PASS variants=3 push_failures=522 query_failures=3 success_controls=3 total=528");
}
