use super::*;
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
fn anyk()->K{let words:[u32;4]=kani::any();for x in words{kani::assume(x<0x7fffffff);}q(words)}
fn anye()->E{E::new(anyk(),anyk())}
fn error(i:u8)->Error{match i%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn code(e:Error)->u8{match e{Error::Parse=>0,Error::Semantic=>1,Error::Transcript=>2,Error::Relation=>3,Error::Merkle=>4,Error::Query=>5,Error::Checkpoint=>6,Error::Allocation=>7}}
fn reply()->Result<E,Error>{if kani::any(){Ok(anye())}else{Err(error(kani::any()))}}
fn encode(r:Result<E,Error>)->reference::Reply{r.map(|x|x.to_limbs()).map_err(code)}
fn result(r:Result<(),Error>)->Result<(),u8>{r.map_err(code)}
fn source_finish(v:&View<'_>,p:&Prepared,a:&Accumulator,obs:Observer,log:&mut Log)->Result<(),Error> {
    let mut claim=p.claim;
    claim=round(v.round0,p.alpha[0],claim,0,log)?;
    if p.variant.folds()==2 {claim=round(v.round1,p.alpha[1],claim,1,log)?;}
    let weights=new_weights(p.variant,&p.semantic_alpha,&p.z,log)?;
    let pair=pair(&weights,&p.alpha[..p.variant.folds()],v.final_message,p.kappa,log)?;
    crate::trace::value(16,0,pair);crate::trace::value(16,1,claim);
    if pair!=claim {return Err(Error::Relation);}
    observed_mark(obs,Phase::Relation,log);
    let actual=dot(v.final_message,&a.weights,log)?;
    crate::trace::value(17,0,actual);crate::trace::value(17,1,a.rhs);
    if a.next!=22||actual!=a.rhs {return Err(Error::Query);}
    observed_mark(obs,Phase::Final,log);Ok(())
}
fn canonical_message(bytes:&[u8],fields:usize){for i in 0..fields{for j in 0..8{let at=32*i+4*j;let word=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);kani::assume(word<0x7fffffff);}}}
fn exercise(group:u8){
 let bytes:[u8;2528]=kani::any();
 let p=Prepared{variant:Variant::S2,roots:kani::any(),gamma:anye(),kappa:anye(),alpha:[anye(),anye()],rho:anyk(),queries:kani::any(),semantic_alpha:core::array::from_fn(|_|anyk()),z:core::array::from_fn(|_|SecureCirclePoint{x:anyk(),y:anyk()}),claim:anye(),state:kani::any()};
 let v=View{variant:p.variant,semantic:&[],y1:&[],inactive:anye(),round0:&bytes[..224],folded_root:None,round1:&bytes[256..480],final_message:&bytes[480..],query_bytes:&[]};
 let weight_values:[K;64]=core::array::from_fn(|_|q(kani::any()));let a=Accumulator{weights:weight_values.to_vec(),rhs:anye(),power:anyk(),next:kani::any()};
 let value=Weights{variant:p.variant,factors:core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|anyk()))),points:core::array::from_fn(|_|core::array::from_fn(|_|anyk())),extra:[anyk(),anyk()]};
 let mut log=Log{r0:reply(),r1:reply(),new_error:if kani::any(){Some(error(kani::any()))}else{None},new_value:Some(Box::new(value)),pair:reply(),dot:reply(),events:[255;7],len:0,rounds:[None,None],new_args:None,new_ptr:core::ptr::null(),pair_args:None,dot_args:None};
 let mut expected=reference::finish_ref(p.variant.folds()==2,a.next,a.rhs.to_limbs(),reference::Replies{round0:if cfg!(NGM_invert)&&group==0{match encode(log.r0){Ok(_)=>Err(0),Err(e)=>Err(if e==0{1}else{0})}}else{encode(log.r0)},round1:encode(log.r1),weights:match log.new_error{Some(e)=>Err(code(e)),None=>Ok(())},pair:encode(log.pair),dot:encode(log.dot)});
 let r=source_finish(&v,&p,&a,None,&mut log);
 if cfg!(NGM_invert){match group{
 1=>expected.len=if expected.len==7{6}else{expected.len+1},
 2=>log.events[0]=255,
 3=>if let Some(x)=&mut log.rounds[0]{x.ptr=x.ptr.wrapping_add(1);},
 4=>if let Some(x)=&mut log.rounds[1]{x.ptr=x.ptr.wrapping_add(1);},
 5=>if let Some(x)=&mut log.new_args{x.1=x.1.wrapping_add(1);},
 6=>if let Some(x)=&mut log.pair_args{x.alpha=x.alpha.wrapping_add(1);},
 7=>if let Some(x)=&mut log.dot_args{x.weights=x.weights.wrapping_add(1);},_=>{}}}
 let good=match group{
 0=>result(r)==expected.result,
 1=>log.len==expected.len,
 2=>{let i:usize=kani::any();kani::assume(i<7);log.events[i]==expected.events[i]},
 3=>match &log.rounds[0]{Some(x)=>x.ptr==v.round0.as_ptr()&&x.len==v.round0.len()&&x.alpha==p.alpha[0]&&x.claim==p.claim&&x.round==0,None=>false},
 4=>match &log.rounds[1]{Some(x)=>x.ptr==v.round1.as_ptr()&&x.len==v.round1.len()&&x.alpha==p.alpha[1]&&Some(x.claim)==log.r0.ok()&&x.round==1,None=>log.r0.is_err()||p.variant.folds()!=2},
 5=>match log.new_args{Some((variant,alpha,z))=>variant==p.variant&&alpha==p.semantic_alpha.as_ptr()&&z==p.z.as_ptr(),None=>true},
 6=>match &log.pair_args{Some(x)=>x.weights==log.new_ptr&&x.alpha==p.alpha.as_ptr()&&x.folds==p.variant.folds()&&x.bytes==v.final_message.as_ptr()&&x.len==v.final_message.len()&&x.kappa==p.kappa,None=>true},
 7=>match &log.dot_args{Some(x)=>x.bytes==v.final_message.as_ptr()&&x.len==v.final_message.len()&&x.weights==a.weights.as_ptr()&&x.width==64,None=>true},_=>false};
 assert!(good);
}
macro_rules! gate{($n:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(65)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $n(){exercise($g)}};}
gate!(finish_control_0,0);
gate!(finish_control_1,1);
gate!(finish_control_2,2);
gate!(finish_control_3,3);
gate!(finish_control_4,4);
gate!(finish_control_5,5);
gate!(finish_control_6,6);
gate!(finish_control_7,7);
gate!(finish_control_rename,0);
