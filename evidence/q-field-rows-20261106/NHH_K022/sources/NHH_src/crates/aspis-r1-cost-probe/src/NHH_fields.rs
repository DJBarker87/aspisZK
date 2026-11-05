#![allow(non_snake_case)]
use aspis_core::field::{M31,CM31,QM31,WideExact,P};
use aspis_core::r0::scalar::CodeField;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn q(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn cm(x:CM31)->[u32;2]{[x.a.0,x.b.0]}
fn w(x:WideExact)->[u32;8]{let a=q(x.c0());let b=q(x.c1());[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]]}
fn check(actual:bool){if cfg!(NHH_invert){assert!(!actual)}else{assert!(actual)}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn m31_embed(){let x:u32=kani::any();let out=<M31 as CodeField>::from_m31(M31(x));check(out.0==x%P);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn cm31_embed(){let x:u32=kani::any();let out=<CM31 as CodeField>::from_m31(M31(x));check(cm(out)==[x%P,0]);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn qm31_embed(){let x:u32=kani::any();let out=<QM31 as CodeField>::from_m31(M31(x));check(q(out)==[x%P,0,0,0]);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn wide_embed(){let x:u32=kani::any();let out=<WideExact as CodeField>::from_m31(M31(x));check(w(out)==[x%P,0,0,0,0,0,0,0]);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn cm_inherent(){let x:u32=kani::any();let out=CM31::from_m31(M31(x));check(cm(out)==[x,0]);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn qm_neg(){let a:[u32;4]=kani::any();kani::assume(a[0]<P&&a[1]<P&&a[2]<P&&a[3]<P);let x=QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}};let out=x.neg();let n=|v:u32|if v==0{0}else{P-v};check(q(out)==[n(a[0]),n(a[1]),n(a[2]),n(a[3])]);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn copy_control(){let src:[u8;32]=kani::any();let mut dst=[0u8;32];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),32)};check(dst==src);}

#[derive(Clone,Copy)]
struct NHH_Event{kind:u8,a:M31,b:M31,out:M31}
struct NHH_Log{events:[NHH_Event;5],len:usize}
fn NHH_event(log:&mut NHH_Log,kind:u8,a:M31,b:M31)->M31{
 assert!(a.0<P&&b.0<P&&log.len<5);
 let out=M31(kani::any());kani::assume(out.0<P);
 log.events[log.len]=NHH_Event{kind,a,b,out};log.len+=1;out
}
fn NHH_product(log:&mut NHH_Log,a:M31,b:M31)->M31{NHH_event(log,0,a,b)}
fn NHH_backend(log:&mut NHH_Log,a:M31)->M31{NHH_event(log,1,a,M31(0))}
fn NHH_fixed(log:&mut NHH_Log,input:CM31)->CM31{

        let norm = NHH_product(log,input.a,input.a).add(NHH_product(log,input.b,input.b));
        let inv_norm = NHH_backend(log,norm);
        CM31 {
            a: NHH_product(log,input.a,inv_norm),
            b: NHH_product(log,input.b.neg(),inv_norm),
        }
    
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn cm_inverse_log(){
 let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P&&b<P&&(a!=0||b!=0));
 let input=CM31{a:M31(a),b:M31(b)};
 let e=NHH_Event{kind:0,a:M31(0),b:M31(0),out:M31(0)};
 let mut log=NHH_Log{events:[e;5],len:0};let out=NHH_fixed(&mut log,input);
 let n=log.events[0].out.add(log.events[1].out);let inv=log.events[2].out;
 let property=log.len==5&&log.events[0].kind==0&&log.events[0].a==input.a&&log.events[0].b==input.a&&
 log.events[1].kind==0&&log.events[1].a==input.b&&log.events[1].b==input.b&&
 log.events[2].kind==1&&log.events[2].a==n&&log.events[2].b==M31(0)&&
 log.events[3].kind==0&&log.events[3].a==input.a&&log.events[3].b==inv&&
 log.events[4].kind==0&&log.events[4].a==input.b.neg()&&log.events[4].b==inv&&
 out.a==log.events[3].out&&out.b==log.events[4].out;
 check(property);
}
