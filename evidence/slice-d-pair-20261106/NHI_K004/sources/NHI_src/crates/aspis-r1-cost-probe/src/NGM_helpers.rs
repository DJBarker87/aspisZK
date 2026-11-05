use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
mod reference{include!("NGM_helper_reference.rs");}
fn q(x:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
fn wide(x:[u32;8])->E{E::new(q([x[0],x[1],x[2],x[3]]),q([x[4],x[5],x[6],x[7]]))}
fn words()->[u32;8]{let out:[u32;8]=kani::any();for x in out{kani::assume(x<0x7fffffff);}out}
fn encode(bytes:&mut[u8],offset:usize,value:[u32;8]){for j in 0..8{bytes[offset+4*j..offset+4*j+4].copy_from_slice(&value[j].to_le_bytes());}}
struct PolyLog{reply:E,left:[u32;8],right:[u32;8],calls:usize,order:u8,ptr:*const u8,len:usize,index:usize,value:[u32;8]}
fn product(a:E,x:E,log:&mut PolyLog)->E{log.left=a.to_limbs();log.right=x.to_limbs();log.calls+=1;log.order=1;log.reply}
fn coefficient(bytes:&[u8],i:usize,log:&mut PolyLog)->E{let selected=&bytes[32*i..32*(i+1)];log.ptr=selected.as_ptr();log.len=selected.len();log.index=i;log.order=if log.order==1{2}else{255};let value=field(bytes,i);log.value=value.to_limbs();value}
fn source_polynomial_step(bytes:&[u8],x:E,a:E,i:usize,log:&mut PolyLog)->E{product(a,x,log).add(coefficient(bytes,i,log))}
fn poly_exercise(group:u8){
 if group==5{let mut calls=0usize;let mut trace=[99usize;7];let _=(0..7).rev().fold(E::ZERO,|a,i|{trace[calls]=i;calls+=1;a});let i:usize=kani::any();kani::assume(i<7);if cfg!(NGM_invert){trace[i]^=1;}assert!(calls==7&&trace[i]==6-i);return;}
 let a=words();let x=words();let p=words();let c=words();let i:usize=kani::any();kani::assume(i<7);let mut bytes:[u8;224]=kani::any();encode(&mut bytes,32*i,c);
 let mut log=PolyLog{reply:wide(p),left:[0;8],right:[0;8],calls:0,order:0,ptr:core::ptr::null(),len:0,index:0,value:[0;8]};
 let actual=source_polynomial_step(&bytes,wide(x),wide(a),i,&mut log).to_limbs();let mut expected=reference::polynomial_step_ref(p,c);
 if cfg!(NGM_invert){match group{0=>expected[0]^=1,1=>expected[4]^=1,2=>log.left[0]^=1,3=>log.index=log.index.wrapping_add(1),4=>log.order=255,_=>{}}}
 let good=match group{0=>(0..4).all(|j|actual[j]==expected[j]),1=>(4..8).all(|j|actual[j]==expected[j]),2=>log.left==a&&log.right==x,3=>log.ptr==bytes.as_ptr().wrapping_add(32*i)&&log.len==32&&log.index==i&&log.value==c,4=>log.order==2&&log.calls==1,_=>false};assert!(good);
}
struct RoundLog{scaled:E,polynomial:E,left:[u32;8],factor:u32,scale_calls:usize,poly_args:Option<(*const u8,usize,[u32;8])>,poly_calls:usize}
fn scale(claim:E,factor:M31,log:&mut RoundLog)->E{log.left=claim.to_limbs();log.factor=factor.0;log.scale_calls+=1;log.scaled}
fn polynomial_reply(bytes:&[u8],alpha:E,log:&mut RoundLog)->E{log.poly_args=Some((bytes.as_ptr(),bytes.len(),alpha.to_limbs()));log.poly_calls+=1;log.polynomial}
fn source_round(poly:&[u8],alpha:E,mut claim:E,round:usize,log:&mut RoundLog)->Result<E,Error>{
 let lhs=field(poly,0).add(field(poly,4));let rhs=scale(claim,QUARTER,log);
 crate::trace::value(15,3*round,lhs);crate::trace::value(15,3*round+1,rhs);
 if lhs!=rhs{return Err(Error::Relation);}
 claim=polynomial_reply(poly,alpha,log);crate::trace::value(15,3*round+2,claim);Ok(claim)
}
fn round_exercise(group:u8){let values:[[u32;8];7]=core::array::from_fn(|_|words());let mut bytes=[0u8;224];for i in 0..7{encode(&mut bytes,32*i,values[i]);}
 let alpha=words();let claim=words();let rhs=words();let out=words();let round:usize=kani::any();kani::assume(round<2);
 let mut log=RoundLog{scaled:wide(rhs),polynomial:wide(out),left:[0;8],factor:0,scale_calls:0,poly_args:None,poly_calls:0};let actual=source_round(&bytes,wide(alpha),wide(claim),round,&mut log);
 let lhs=reference::polynomial_step_ref(values[0],values[4]);let mut expected_rhs=rhs;
 if cfg!(NGM_invert){match group{0=>expected_rhs[0]^=1,1=>log.factor=536870913,2=>if let Some(args)=&mut log.poly_args{args.0=args.0.wrapping_add(1);},_=>{}}}
 let expected=reference::round_ref(lhs,expected_rhs,out);
 let good=match group{0=>match(actual,expected){(Ok(a),Ok(b))=>a.to_limbs()==b,(Err(Error::Relation),Err(3))=>true,_=>false},1=>log.left==claim&&log.factor==536870912&&log.scale_calls==1,2=>log.poly_calls==if lhs==rhs{1}else{0}&&match log.poly_args{Some((ptr,len,a))=>ptr==bytes.as_ptr()&&len==224&&a==alpha,None=>lhs!=rhs},_=>false};assert!(good);
}
macro_rules! gate{($n:ident,$f:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(65)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $n(){$f($g)}};}
gate!(poly_g0,poly_exercise,0);
gate!(poly_g1,poly_exercise,1);
gate!(poly_g2,poly_exercise,2);
gate!(poly_g3,poly_exercise,3);
gate!(poly_g4,poly_exercise,4);
gate!(poly_g5,poly_exercise,5);
gate!(round_g0,round_exercise,0);
gate!(round_g1,round_exercise,1);
gate!(round_g2,round_exercise,2);
