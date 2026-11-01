//! Compositional source gates. Field algebra/traces are the stage-2 premises.
use super::{field, reference};
use field::{M31, CM31, QM31};
#[cfg(kani)] const CAP:usize=256;
#[cfg(not(kani))] const CAP:usize=32768;
static mut EVENTS:[u32;CAP]=[0;CAP];
static mut N:usize=0;
static mut REPLAY:bool=false;
pub fn event(id:u32) {unsafe {let n=N;assert!(n<CAP);if REPLAY {assert_eq!(EVENTS[n],id);}else{EVENTS[n]=id;}N+=1;}}
fn reset() {unsafe {N=0;REPLAY=false;}}
fn replay() -> usize {unsafe {let n=N;N=0;REPLAY=true;n}}
fn finish(n:usize) {assert_eq!(unsafe{N},n);}
fn qm(x:[u32;4])->QM31 {QM31 {c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn raw(x:QM31)->[u32;4] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn rq(x:QM31)->reference::QM31 {let x=raw(x); reference::QM31{c0:reference::CM31{a:reference::M31(x[0]),b:reference::M31(x[1])},c1:reference::CM31{a:reference::M31(x[2]),b:reference::M31(x[3])}}}
fn rr(x:reference::QM31)->QM31 {qm([x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0])}
#[cfg(kani)] fn any_qm()->QM31 {qm(kani::any())}
#[cfg(kani)] fn canonical()->QM31 {let x:[u32;4]=kani::any();for v in x {kani::assume(v<field::P);}qm(x)}
#[cfg(kani)]
#[kani::proof]
fn pole_equal_equivalence() {let a=any_qm();let b=any_qm();assert_eq!(super::pole_actual::equal(a,b),a==b);}
#[cfg(kani)]
#[kani::proof]
fn pole_fold_equivalence() {let c:bool=kani::any();let active:bool=kani::any();let a=any_qm();let b=any_qm();let old=if active {c & (a!=b)}else{c};assert_eq!(super::pole_actual::keep_clear(c,active,a,b),old);}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(10)]
fn pole_two_row_equivalence() {
 let values:[[[QM31;2];2];2]=core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|any_qm())));
 let chi=any_qm();let mut masks=[0u16;64];masks[0]=kani::any();let mut old=true;
 for (row,sides) in values.iter().enumerate() {if masks[row>>4]&(1<<(row&15))==0 {continue;}for v in sides.iter().flatten(){old &= chi!=*v;}}
 assert_eq!(old,super::pole_actual::all_slots_clear(&values,&masks,chi));
}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(10)]
fn pole_two_run_scan() {
 let a:[[[QM31;2];2];2]=core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|any_qm())));
 let b:[[[QM31;2];2];2]=core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|any_qm())));
 let chi=any_qm();let psi=any_qm();let mut masks=[0u16;64];masks[0]=kani::any();
 reset();let _=super::pole_instrumented::all_slots_clear(&a,&masks,chi);let n=replay();let _=super::pole_instrumented::all_slots_clear(&b,&masks,psi);finish(n);
}

#[cfg(kani)] struct Oracle {op:[u8;48],a:[[u32;4];48],b:[[u32;4];48],out:[[u32;4];48],n:usize,replay:bool}
#[cfg(kani)] static mut O:Oracle=Oracle{op:[0;48],a:[[0;4];48],b:[[0;4];48],out:[[0;4];48],n:0,replay:false};
#[cfg(kani)] fn leaf(op:u8,a:QM31,b:QM31)->QM31 {unsafe {let n=O.n;O.n+=1;assert!(n<48);if O.replay{assert_eq!(O.op[n],op);assert_eq!(O.a[n],raw(a));assert_eq!(O.b[n],raw(b));qm(O.out[n])}else{let v=canonical();O.op[n]=op;O.a[n]=raw(a);O.b[n]=raw(b);O.out[n]=raw(v);v}}}
#[cfg(kani)] fn c_add(a:QM31,b:QM31)->QM31{leaf(1,a,b)}
#[cfg(kani)] fn c_mul(a:QM31,b:QM31)->QM31{leaf(2,a,b)}
#[cfg(kani)] fn c_scalar(a:QM31,b:M31)->QM31{leaf(3,a,QM31::from_cm31(CM31::from_m31(b)))}
#[cfg(kani)] fn r_add(a:reference::QM31,b:reference::QM31)->reference::QM31{rq(leaf(1,rr(a),rr(b)))}
#[cfg(kani)] fn r_mul(a:reference::QM31,b:reference::QM31)->reference::QM31{rq(leaf(2,rr(a),rr(b)))}
#[cfg(kani)] fn r_scalar(a:reference::QM31,b:reference::M31)->reference::QM31{rq(leaf(3,rr(a),QM31::from_cm31(CM31::from_m31(M31(b.0)))))}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(50)]
#[kani::stub(field::QM31::add,c_add)]
#[kani::stub(field::QM31::mul,c_mul)]
#[kani::stub(field::QM31::mul_m31,c_scalar)]
#[kani::stub(reference::QM31::add,r_add)]
#[kani::stub(reference::QM31::mul,r_mul)]
#[kani::stub(reference::QM31::mul_m31,r_scalar)]
fn pole_compression_equivalence() {
 let tag=canonical().c0.a;let lambda=canonical();let values:[M31;16]=core::array::from_fn(|_|canonical().c0.a);
 let rvalues=values.map(|v|reference::M31(v.0));
 let expected=super::pole_compression_reference::compress_tagged_tuple(reference::M31(tag.0),&rvalues,rq(lambda));
 let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}
 let actual=super::pole_compression::compress_tagged_tuple(tag,&values,lambda);
 assert_eq!(unsafe{O.n},n);assert_eq!(raw(actual),raw(rr(expected)));
}
#[cfg(kani)] fn t_add(_:QM31,_:QM31)->QM31{event(20);canonical()}
#[cfg(kani)] fn t_mul(_:QM31,_:QM31)->QM31{event(21);canonical()}
#[cfg(kani)] fn t_scalar(_:QM31,_:M31)->QM31{event(22);canonical()}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(20)]
#[kani::stub(field::QM31::add,t_add)]
#[kani::stub(field::QM31::mul,t_mul)]
#[kani::stub(field::QM31::mul_m31,t_scalar)]
fn pole_two_run_compression() {
 let a:[M31;16]=core::array::from_fn(|_|canonical().c0.a);let b:[M31;16]=core::array::from_fn(|_|canonical().c0.a);
 let tag=canonical().c0.a;let lambda=canonical();let psi=canonical();
 reset();let _=super::pole_compression_instrumented::compress_tagged_tuple(tag,&a,lambda);let n=replay();let _=super::pole_compression_instrumented::compress_tagged_tuple(tag,&b,psi);finish(n);
}
#[test]
fn pole_full_shape_two_run_trace_and_verdict() {
 fn sample(seed:&mut u64)->QM31 {qm(core::array::from_fn(|_|{*seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);((*seed>>32) as u32)%field::P}))}
 let mut seed=41;let a:Vec<_>=(0..1024).map(|_|core::array::from_fn(|_|core::array::from_fn(|_|sample(&mut seed)))).collect();
 let mut b:Vec<_>=(0..1024).map(|_|core::array::from_fn(|_|core::array::from_fn(|_|sample(&mut seed)))).collect();let chi=sample(&mut seed);let psi=sample(&mut seed);
 let masks=core::array::from_fn(|i|if i%2==0 {0xAAAA}else{0x5555});b[1022][1][1]=psi;
 reset();let clear=super::pole_instrumented::all_slots_clear(&a,&masks,chi);let n=unsafe{N};let calls=(0..n).filter(|&i|unsafe{EVENTS[i]==1}).count();assert_eq!(calls,4096);
 let n=replay();let pole=super::pole_instrumented::all_slots_clear(&b,&masks,psi);finish(n);assert!(clear);assert!(!pole);
 for values in [&a,&b] {let old=values.iter().enumerate().filter(|(r,_)|masks[r>>4]&(1<<(r&15))!=0).flat_map(|(_,s)|s.iter().flatten()).all(|v|*v!=psi);assert_eq!(old,super::pole_actual::all_slots_clear(values,&masks,psi));}
 // Same trace when the very first active slot is a pole, or all rows inactive.
 b[0][0][0]=psi;let masks=[0xFFFF;64];reset();let _=super::pole_instrumented::all_slots_clear(&a,&masks,chi);let n=replay();assert!(!super::pole_instrumented::all_slots_clear(&b,&masks,psi));finish(n);let n=replay();assert!(super::pole_instrumented::all_slots_clear(&b,&[0;64],psi));finish(n);
 let vals:[M31;16]=core::array::from_fn(|_|sample(&mut seed).c0.a);let other:[M31;16]=core::array::from_fn(|_|sample(&mut seed).c0.a);
 reset();let x=super::pole_compression_instrumented::compress_tagged_tuple(M31(7),&vals,chi);let n=replay();let _=super::pole_compression_instrumented::compress_tagged_tuple(M31(7),&other,psi);finish(n);
 assert_eq!(x,super::pole_compression::compress_tagged_tuple(M31(7),&vals,chi));
 println!("1024 rows, 4096 eager comparisons; full trace replay equal; 16-limb compression replay equal");
}
