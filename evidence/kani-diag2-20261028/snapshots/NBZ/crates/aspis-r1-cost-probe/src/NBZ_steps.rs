// NBZ one-window gates. All carriers are actual native Vecs, fully initialized
// element by element with symbolic scalars. Initialization is harness setup;
// the checked target is a single native borrow/copy/store or source step.
extern crate alloc;
include!("KMX_stubs.rs");
use super::*;
use aspis_core::field::CM31;
fn NBZ_raw(cap:usize)->Vec<[u64;4]> {
 let mut v=Vec::<[u64;4]>::with_capacity(cap);
 for i in 0..64 {for k in 0..4 {unsafe {core::ptr::addr_of_mut!((*v.as_mut_ptr().add(i))[k]).write(kani::any());}}}
 unsafe {v.set_len(64);}v
}
fn NBZ_weights(cap:usize)->Vec<K> {
 let mut v=Vec::<K>::with_capacity(cap);
 for i in 0..64 {unsafe {
  core::ptr::addr_of_mut!((*v.as_mut_ptr().add(i)).c0.a.0).write(kani::any());
  core::ptr::addr_of_mut!((*v.as_mut_ptr().add(i)).c0.b.0).write(kani::any());
  core::ptr::addr_of_mut!((*v.as_mut_ptr().add(i)).c1.a.0).write(kani::any());
  core::ptr::addr_of_mut!((*v.as_mut_ptr().add(i)).c1.b.0).write(kani::any());
 }}
 unsafe {v.set_len(64);}v
}
fn NBZ_lines(cap:usize)->Vec<M31> {
 let mut v=Vec::<M31>::with_capacity(cap);
 for i in 0..10 {unsafe {core::ptr::addr_of_mut!((*v.as_mut_ptr().add(i)).0).write(kani::any());}}
 unsafe {v.set_len(10);}v
}
fn NBZ_inverses(cap:usize)->Vec<[M31;5]> {
 let mut v=Vec::<[M31;5]>::with_capacity(cap);
 for i in 0..10 {for k in 0..5 {unsafe {core::ptr::addr_of_mut!((*v.as_mut_ptr().add(i))[k].0).write(kani::any());}}}
 unsafe {v.set_len(10);}v
}
fn NBZ_cap<T>(n:usize)->usize {let cap:usize=kani::any();kani::assume(cap>=n&&cap<=isize::MAX as usize/core::mem::size_of::<T>());cap}
fn NBZ_qwords(q:K)->[u32;4] {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn NBZ_q(w:[u32;4])->K {K{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
mod NBZ_field {
use super::*;
use aspis_core::field::{QM31,WideExact};
const MOD:u64=2147483647;
fn m(a:u32,b:u32)->u32{((u64::from(a)*u64::from(b))%MOD)as u32}
fn a(x:u32,y:u32)->u32{((u64::from(x)+u64::from(y))%MOD)as u32}
fn d(x:u32,y:u32)->u32{((u64::from(x)+MOD-u64::from(y))%MOD)as u32}
fn cw(x:CM31)->[u32;2]{[x.a.0,x.b.0]}
fn qw(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn c(x:[u32;2])->CM31{CM31{a:M31(x[0]),b:M31(x[1])}}
fn q(x:[u32;4])->QM31{QM31{c0:c([x[0],x[1]]),c1:c([x[2],x[3]])}}
fn ca(x:[u32;2],y:[u32;2])->[u32;2]{[a(x[0],y[0]),a(x[1],y[1])]}
fn cd(x:[u32;2],y:[u32;2])->[u32;2]{[d(x[0],y[0]),d(x[1],y[1])]}
fn cm(x:[u32;2],y:[u32;2])->[u32;2]{let t=m(x[0],y[0]);let u=m(x[1],y[1]);
 let cross=(((u64::from(x[0])+u64::from(x[1]))*(u64::from(y[0])+u64::from(y[1])))%MOD)as u32;
 [d(t,u),d(d(cross,t),u)]}
fn cr(x:[u32;2])->[u32;2]{[d(a(x[0],x[0]),x[1]),a(x[0],a(x[1],x[1]))]}
fn qa(x:[u32;4],y:[u32;4])->[u32;4]{core::array::from_fn(|i|a(x[i],y[i]))}
fn qd(x:[u32;4],y:[u32;4])->[u32;4]{core::array::from_fn(|i|d(x[i],y[i]))}
fn qm(x:[u32;4],y:[u32;4])->[u32;4]{let x0=[x[0],x[1]];let x1=[x[2],x[3]];let y0=[y[0],y[1]];let y1=[y[2],y[3]];
 let t=cm(x0,y0);let u=cm(x1,y1);let v=cm(ca(x0,x1),ca(y0,y1));let lo=ca(t,cr(u));let hi=cd(cd(v,t),u);[lo[0],lo[1],hi[0],hi[1]]}
fn domain<const N:usize>(x:[u32;N]){for i in 0..N{assert!(u64::from(x[i])<MOD,"LPh field stub domain");}}
fn chosen<const N:usize>(value:[u32;N])->[u32;N]{let out:[u32;N]=kani::any();for i in 0..N{kani::assume(out[i]==value[i]);kani::assume(u64::from(out[i])<MOD);}out}
pub fn m31(x:M31,y:M31)->M31{domain([x.0,y.0]);let z=M31(chosen([m(x.0,y.0)])[0]);unsafe {let i=MC;assert!(i<8);MX[i]=x.0;MY[i]=y.0;MO[i]=z.0;MC+=1;}z}
pub fn cm31(x:CM31,y:CM31)->CM31{domain(cw(x));domain(cw(y));c(chosen(cm(cw(x),cw(y))))}
pub fn qm31(x:QM31,y:QM31)->QM31{domain(qw(x));domain(qw(y));let z=q(chosen(qm(qw(x),qw(y))));unsafe{let i=QC;assert!(i<4);QX[i]=qw(x);QY[i]=qw(y);QO[i]=qw(z);QC+=1;}z}
pub fn scalar(x:QM31,y:M31)->QM31{domain(qw(x));domain([y.0]);let z=q(chosen(qw(x).map(|v|m(v,y.0))));unsafe {let i=SC;assert!(i<16);SX[i]=qw(x);SY[i]=y.0;SO[i]=qw(z);SC+=1;}z}
pub fn by_r(x:CM31)->CM31{domain(cw(x));c(chosen(cr(cw(x))))}
pub fn wide(x:WideExact,y:WideExact)->WideExact{domain(x.to_limbs());domain(y.to_limbs());
 let x0=qw(x.c0());let x1=qw(x.c1());let y0=qw(y.c0());let y1=qw(y.c1());
 let t=qm(x0,y0);let u=qm(x1,y1);let cross=qm(qa(x0,x1),qa(y0,y1));let r=cr([u[2],u[3]]);
 let lo=qa(t,[r[0],r[1],u[0],u[1]]);let hi=qd(qd(cross,t),u);
 let z=WideExact::from_limbs(chosen([lo[0],lo[1],lo[2],lo[3],hi[0],hi[1],hi[2],hi[3]])).unwrap();unsafe {let i=WC;assert!(i<4);WX[i]=x.to_limbs();WY[i]=y.to_limbs();WO[i]=z.to_limbs();WC+=1;}z}

pub static mut QC:usize=0;pub static mut QX:[[u32;4];4]=[[0;4];4];pub static mut QY:[[u32;4];4]=[[0;4];4];pub static mut QO:[[u32;4];4]=[[0;4];4];
pub static mut MC:usize=0;pub static mut MX:[u32;8]=[0;8];pub static mut MY:[u32;8]=[0;8];pub static mut MO:[u32;8]=[0;8];
pub static mut SC:usize=0;pub static mut SX:[[u32;4];16]=[[0;4];16];pub static mut SY:[u32;16]=[0;16];pub static mut SO:[[u32;4];16]=[[0;4];16];
pub static mut WC:usize=0;pub static mut WX:[[u32;8];4]=[[0;8];4];pub static mut WY:[[u32;8];4]=[[0;8];4];pub static mut WO:[[u32;8];4]=[[0;8];4];
}

fn NBZ_e()->E {let w:[u32;8]=kani::any();for x in w {kani::assume(x<2147483647);}E::from_limbs(w).unwrap()}
// One literal inner Horner call from both frozen fold bodies.
fn NBZ_horner_expression(alpha:E,h:E,previous:E)->E {h.add(alpha.mul(previous))}
fn NBZ_horner_case(negative:bool){
 let alpha=NBZ_e();let h=NBZ_e();let previous=NBZ_e();let k:usize=kani::any();kani::assume(k<8);
 let out=NBZ_horner_expression(alpha,h,previous);
 unsafe {
  assert_eq!(NBZ_field::WC,1);assert_eq!(NBZ_field::WX[0][k],alpha.to_limbs()[k]);assert_eq!(NBZ_field::WY[0][k],previous.to_limbs()[k]);
  let z=E::from_limbs(NBZ_field::WO[0]).unwrap();let expected=h.add(z).to_limbs()[k];
  if negative{assert_ne!(out.to_limbs()[k],expected);}else{assert_eq!(out.to_limbs()[k],expected);}
  assert!(out.to_limbs()[k]<2147483647);
 }
 kani::cover!(k==0);kani::cover!(k==7);
}
// One U64 word within an actual full 64-row Vec, arbitrary allocation capacity.
fn NBZ_raw_word_case(negative:bool) {
 let cap=NBZ_cap::<[u64;4]>(64);let mut raw=NBZ_raw(cap);let ptr=raw.as_ptr();
 let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let l:usize=kani::any();
 kani::assume(i<64&&j<64&&k<4&&l<4);let before=raw[j][l];let reply:u64=kani::any();
 raw[i][k..k+1].copy_from_slice(&[reply]);
 let expected=if i==j&&k==l{reply}else{before};
 if negative{assert_ne!(raw[j][l],expected);}else{assert_eq!(raw[j][l],expected);}
 assert_eq!(raw.as_ptr(),ptr);assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);
 kani::cover!(i==63&&k==3);kani::cover!(i!=j);kani::cover!(i==j&&k!=l);kani::cover!(cap>64);
}
static mut NBZ_RIN:[u64;4]=[0;4];static mut NBZ_ROUT:[u32;4]=[0;4];static mut NBZ_RCALLS:usize=0;
fn NBZ_reducer(x:u64)->M31 {unsafe{let i=NBZ_RCALLS;assert!(i<4);NBZ_RCALLS+=1;assert_eq!(x,NBZ_RIN[i]);M31(NBZ_ROUT[i])}}
fn NBZ_finish_case(negative:bool) {
 let rc=NBZ_cap::<[u64;4]>(64);let wc=NBZ_cap::<K>(64);
 let b=BatchedWeights{raw:NBZ_raw(rc),terms:kani::any()};let mut out=NBZ_weights(wc);
 let i:usize=kani::any();kani::assume(i<=64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let before=NBZ_qwords(out[j])[k];let optr=out.as_ptr();let bptr=b.raw.as_ptr();let oldterms=b.terms;
 let reply:[u32;4]=kani::any();for x in reply{kani::assume(x<2147483647);}
 unsafe{NBZ_ROUT=reply;if i<64 {NBZ_RIN=b.raw[i];}}
 {let mut it=out.iter_mut().enumerate();if i>0 {let _=it.nth(i-1);}if let Some((index,w))=it.next(){*w=b.value(index);}}
 let expected=if i==j {reply[k]}else{before};
 if negative{assert_ne!(NBZ_qwords(out[j])[k],expected);}else{assert_eq!(NBZ_qwords(out[j])[k],expected);}
 assert_eq!(out.as_ptr(),optr);assert_eq!(out.len(),64);assert_eq!(out.capacity(),wc);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(b.raw.capacity(),rc);assert_eq!(b.terms,oldterms);
 unsafe{assert_eq!(NBZ_RCALLS,if i<64{4}else{0});}
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i==64);kani::cover!(i!=j);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(65)]
fn NBZ_raw_word(){NBZ_raw_word_case(false);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(65)]
fn NBZ_raw_word_negative(){NBZ_raw_word_case(true);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(65)]
#[kani::stub(aspis_core::field::WideExact::mul,NBZ_field::wide)]
fn NBZ_horner(){NBZ_horner_case(false);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(65)]
#[kani::stub(aspis_core::field::WideExact::mul,NBZ_field::wide)]
fn NBZ_horner_negative(){NBZ_horner_case(true);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(65)]
#[kani::stub(aspis_core::field::M31::reduce_u64,NBZ_reducer)]
fn NBZ_finish(){NBZ_finish_case(false);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(65)]
#[kani::stub(aspis_core::field::M31::reduce_u64,NBZ_reducer)]
fn NBZ_finish_negative(){NBZ_finish_case(true);}
