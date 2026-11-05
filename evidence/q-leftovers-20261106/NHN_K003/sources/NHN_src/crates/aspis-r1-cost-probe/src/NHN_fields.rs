#![allow(non_snake_case)]
use aspis_core::field::{M31,CM31,P};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct NHN_Event{kind:u8,a:M31,b:M31,out:M31}
struct NHN_Log{events:[NHN_Event;5],len:usize}
fn NHN_event(log:&mut NHN_Log,kind:u8,a:M31,b:M31,out:M31)->M31{
 assert!(a.0<P&&b.0<P&&out.0<P&&log.len<5);
 log.events[log.len]=NHN_Event{kind,a,b,out};log.len+=1;out
}
fn NHN_product(log:&mut NHN_Log,a:M31,b:M31)->M31{
 let out=M31(kani::any());kani::assume(out.0<P);NHN_event(log,0,a,b,out)
}
fn NHN_inverse_stub(a:M31)->M31{
 assert!(a.0<P);let out=M31(kani::any());kani::assume(out.0<P);out
}
fn NHN_backend(log:&mut NHN_Log,a:M31,inverse:fn(M31)->M31)->M31{
 let out=inverse(a);NHN_event(log,1,a,M31(0),out)
}
fn NHN_instantiated(log:&mut NHN_Log,input:CM31,inverse:fn(M31)->M31)->CM31{

        let norm = NHN_product(log,input.a,input.a).add(NHN_product(log,input.b,input.b));
        let inv_norm = NHN_backend(log,norm,inverse);
        CM31 {
            a: NHN_product(log,input.a,inv_norm),
            b: NHN_product(log,input.b.neg(),inv_norm),
        }
    
}
fn NHN_check(){
 let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P&&b<P&&(a!=0||b!=0));
 let input=CM31{a:M31(a),b:M31(b)};
 let e=NHN_Event{kind:0,a:M31(0),b:M31(0),out:M31(0)};
 let mut log=NHN_Log{events:[e;5],len:0};
 let out=NHN_instantiated(&mut log,input,M31::inv);
 if cfg!(NHN_bad_argument){log.events[0].a=M31(if a==0{1}else{0});}
 let n=log.events[0].out.add(log.events[1].out);let inv=log.events[2].out;
 assert!(log.len==5&&log.events[0].kind==0&&log.events[0].a==input.a&&log.events[0].b==input.a&&
 log.events[1].kind==0&&log.events[1].a==input.b&&log.events[1].b==input.b&&
 log.events[2].kind==1&&log.events[2].a==n&&log.events[2].b==M31(0)&&
 log.events[3].kind==0&&log.events[3].a==input.a&&log.events[3].b==inv&&
 log.events[4].kind==0&&log.events[4].a==input.b.neg()&&log.events[4].b==inv&&
 out.a==log.events[3].out&&out.b==log.events[4].out);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(M31::inv,NHN_inverse_stub)]
#[kani::unwind(80)]
fn NHN_inv_constant(){NHN_check()}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(M31::inv,NHN_inverse_stub)]
#[kani::unwind(80)]
fn NHN_inv_constant_renamed(){NHN_check()}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NHN_copy_control(){let src:[u8;32]=kani::any();let mut dst=[0u8;32];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),32)};if cfg!(NHN_bad_argument){dst[0]=src[0].wrapping_add(1)};assert!(dst==src);}
