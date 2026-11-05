from pathlib import Path
import json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/'
ref='''pub type Word=[u32;8];
pub type Reply=Result<Word,u8>;
pub struct Replies {pub round0:Reply,pub round1:Reply,pub weights:Result<(),u8>,pub pair:Reply,pub dot:Reply}
pub struct Observed {pub result:Result<(),u8>,pub events:[u8;7],pub len:usize}
fn event(o:&mut Observed,tag:u8){o.events[o.len]=tag;o.len+=1;}
pub fn finish_ref(two:bool,next:usize,rhs:Word,r:Replies)->Observed {
 let mut o=Observed{result:Ok(()),events:[255;7],len:0};
 event(&mut o,0);
 let mut claim=match r.round0 {Ok(x)=>x,Err(e)=>{o.result=Err(e);return o;}};
 if two {event(&mut o,1);claim=match r.round1 {Ok(x)=>x,Err(e)=>{o.result=Err(e);return o;}};}
 event(&mut o,2);if let Err(e)=r.weights{o.result=Err(e);return o;}
 event(&mut o,3);let pair=match r.pair{Ok(x)=>x,Err(e)=>{o.result=Err(e);return o;}};
 if pair!=claim{o.result=Err(3);return o;}
 event(&mut o,4);event(&mut o,5);
 let actual=match r.dot{Ok(x)=>x,Err(e)=>{o.result=Err(e);return o;}};
 if next!=22||actual!=rhs{o.result=Err(5);return o;}
 event(&mut o,6);o
}
'''
(E/'NGM_control_reference.rs.txt').write_text(ref)
src=subprocess.check_output(['git','show','4bb3b3f:'+C+'verifier.rs'],text=True)
i=src.index('pub fn finish_relation(');j=src.index('\n}',i)+2;body=src[i:j]
instrumented=body.replace('pub fn finish_relation(', 'fn source_finish(').replace('obs:Observer)', 'obs:Observer,log:&mut Log)')
for a,b in [('finish_relation_round(v.round0,p.alpha[0],claim,0)','round(v.round0,p.alpha[0],claim,0,log)'),('finish_relation_round(v.round1,p.alpha[1],claim,1)','round(v.round1,p.alpha[1],claim,1,log)'),('Weights::new(p.variant,&p.semantic_alpha,&p.z)','new_weights(p.variant,&p.semantic_alpha,&p.z,log)'),('weights.pair(&p.alpha[..p.variant.folds()],v.final_message,p.kappa)','pair(&weights,&p.alpha[..p.variant.folds()],v.final_message,p.kappa,log)'),('finish_query_dot(v.final_message,&a.weights)','dot(v.final_message,&a.weights,log)'),('mark(obs,Phase::Relation)','observed_mark(obs,Phase::Relation,log)'),('mark(obs,Phase::Final)','observed_mark(obs,Phase::Final,log)')]:
 assert a in instrumented;instrumented=instrumented.replace(a,b)
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
mod reference {include!("NGM_control_reference.rs");}
struct RoundArgs{ptr:*const u8,len:usize,alpha:E,claim:E,round:usize}
struct PairArgs{weights:*const Weights,alpha:*const E,folds:usize,bytes:*const u8,len:usize,kappa:E}
struct DotArgs{bytes:*const u8,len:usize,weights:*const K,width:usize}
struct Log{r0:Result<E,Error>,r1:Result<E,Error>,new_error:Option<Error>,new_value:Option<Box<Weights>>,pair:Result<E,Error>,dot:Result<E,Error>,events:[u8;7],len:usize,rounds:[Option<RoundArgs>;2],new_args:Option<(Variant,*const K,*const SecureCirclePoint)>,new_ptr:*const Weights,pair_args:Option<PairArgs>,dot_args:Option<DotArgs>}
fn event(log:&mut Log,n:u8){log.events[log.len]=n;log.len+=1;}
fn round(poly:&[u8],alpha:E,claim:E,round:usize,log:&mut Log)->Result<E,Error>{event(log,round as u8);log.rounds[round]=Some(RoundArgs{ptr:poly.as_ptr(),len:poly.len(),alpha,claim,round});if round==0{log.r0}else{log.r1}}
fn new_weights(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2],log:&mut Log)->Result<Box<Weights>,Error>{event(log,2);log.new_args=Some((variant,alpha.as_ptr(),z.as_ptr()));if let Some(e)=log.new_error{return Err(e);}let w=log.new_value.take().unwrap();log.new_ptr=&*w;Ok(w)}
fn pair(w:&Weights,alpha:&[E],bytes:&[u8],kappa:E,log:&mut Log)->Result<E,Error>{event(log,3);log.pair_args=Some(PairArgs{weights:w,alpha:alpha.as_ptr(),folds:alpha.len(),bytes:bytes.as_ptr(),len:bytes.len(),kappa});log.pair}
fn dot(bytes:&[u8],weights:&[K],log:&mut Log)->Result<E,Error>{event(log,5);log.dot_args=Some(DotArgs{bytes:bytes.as_ptr(),len:bytes.len(),weights:weights.as_ptr(),width:weights.len()});log.dot}
fn observed_mark(obs:Observer,phase:Phase,log:&mut Log){event(log,if phase==Phase::Relation{4}else{6});super::mark(obs,phase);}
fn q(x:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
fn anyk()->K{q(kani::any())}
fn anye()->E{E::new(anyk(),anyk())}
fn error(i:u8)->Error{match i%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn code(e:Error)->u8{match e{Error::Parse=>0,Error::Semantic=>1,Error::Transcript=>2,Error::Relation=>3,Error::Merkle=>4,Error::Query=>5,Error::Checkpoint=>6,Error::Allocation=>7}}
fn reply()->Result<E,Error>{if kani::any(){Ok(anye())}else{Err(error(kani::any()))}}
fn encode(r:Result<E,Error>)->reference::Reply{r.map(|x|x.to_limbs()).map_err(code)}
fn result(r:Result<(),Error>)->Result<(),u8>{r.map_err(code)}
'''+instrumented+'''
fn exercise(group:u8){
 let bytes:[u8;2496]=kani::any();
 let p=Prepared{variant:match kani::any::<u8>()%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D},roots:[[0;32];2],gamma:E::ZERO,kappa:anye(),alpha:[anye(),anye()],rho:K::ZERO,queries:[0;22],semantic_alpha:core::array::from_fn(|_|anyk()),z:core::array::from_fn(|_|SecureCirclePoint{x:anyk(),y:anyk()}),claim:anye(),state:[0;32]};
 let v=View{variant:p.variant,semantic:&[],y1:&[],inactive:E::ZERO,round0:&bytes[..224],folded_root:None,round1:&bytes[224..448],final_message:&bytes[448..],query_bytes:&[]};
 let a=Accumulator{weights:alloc::vec![K::ZERO;64],rhs:anye(),power:K::ZERO,next:kani::any()};
 let value=Weights{variant:p.variant,factors:core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|anyk()))),points:core::array::from_fn(|_|core::array::from_fn(|_|anyk())),extra:[anyk(),anyk()]};
 let mut log=Log{r0:reply(),r1:reply(),new_error:if kani::any(){Some(error(kani::any()))}else{None},new_value:Some(Box::new(value)),pair:reply(),dot:reply(),events:[255;7],len:0,rounds:[None,None],new_args:None,new_ptr:core::ptr::null(),pair_args:None,dot_args:None};
 let expected=reference::finish_ref(p.variant.folds()==2,a.next,a.rhs.to_limbs(),reference::Replies{round0:encode(log.r0),round1:encode(log.r1),weights:match log.new_error{Some(e)=>Err(code(e)),None=>Ok(())},pair:encode(log.pair),dot:encode(log.dot)});
 let r=source_finish(&v,&p,&a,None,&mut log);
 let good=match group{
 0=>result(r)==expected.result,
 1=>log.len==expected.len,
 2=>{let i:usize=kani::any();kani::assume(i<7);log.events[i]==expected.events[i]},
 3=>match &log.rounds[0]{Some(x)=>x.ptr==v.round0.as_ptr()&&x.len==v.round0.len()&&x.alpha==p.alpha[0]&&x.claim==p.claim&&x.round==0,None=>false},
 4=>match &log.rounds[1]{Some(x)=>x.ptr==v.round1.as_ptr()&&x.len==v.round1.len()&&x.alpha==p.alpha[1]&&Some(x.claim)==log.r0.ok()&&x.round==1,None=>log.r0.is_err()||p.variant.folds()!=2},
 5=>match log.new_args{Some((variant,alpha,z))=>variant==p.variant&&alpha==p.semantic_alpha.as_ptr()&&z==p.z.as_ptr(),None=>true},
 6=>match &log.pair_args{Some(x)=>x.weights==log.new_ptr&&x.alpha==p.alpha.as_ptr()&&x.folds==p.variant.folds()&&x.bytes==v.final_message.as_ptr()&&x.len==v.final_message.len()&&x.kappa==p.kappa,None=>true},
 7=>match &log.dot_args{Some(x)=>x.bytes==v.final_message.as_ptr()&&x.len==v.final_message.len()&&x.weights==a.weights.as_ptr()&&x.width==64,None=>true},_=>false};
 assert!(good != cfg!(NGM_invert));
}
macro_rules! gate{($n:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(65)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $n(){exercise($g)}};}
'''
for g in range(8):code+=f'gate!(finish_control_{g},{g});\n'
code+='gate!(finish_control_rename,0);\n'
files={C+'verifier.rs':src+'\n#[cfg(kani)] #[path="NGM_verifier.rs"] mod NGM_verifier;\n',C+'NGM_verifier.rs':code,C+'NGM_control_reference.rs':ref}
inputs=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());inputs.update(files);(E/'NGM_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NGM_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in files.items()});(E/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,s in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),s.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n)
(E/'NGM_harness.patch').write_text(''.join(patch))
(E/'NGM_CONTROL_ASSOCIATION.json').write_text(json.dumps(dict(frozen_body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),instrumented_sha256=hashlib.sha256(instrumented.encode()).hexdigest(),rule='(y), (ae): source-fission candidate; full typed child Result; local log only; no multiplication',caveat='Caller/callee domains and emitted model association remain OPEN until separately checked'),indent=2)+'\n')
