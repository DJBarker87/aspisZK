use super::*;
#[path="NDN_reference.rs"] mod reference;
fn canon(q:QM31)->bool {q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
pub(super) static mut PRE:[QM31;7]=[QM31::ZERO;7];
pub(super) static mut BLOCK:usize=0;
pub(super) static mut AFTER:[QM31;7]=[QM31::ZERO;7];
pub(super) static mut NEXT:usize=0;
#[cfg(NDN_active_high)]
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn active_high_window(){
 let selectors=Selectors{high:kani::any(),low:kani::any()};
 let pre:[QM31;7]=kani::any();let block:usize=kani::any();let j:usize=kani::any();
 kani::assume(block<64&&j<7);
 let coordinate=reference::active_coordinate(constants::ACTIVE_ROW_MASKS[block]);
 kani::assume(canon(pre[coordinate])&&canon(selectors.high[block]));
 unsafe{PRE=pre;BLOCK=block;}
 let _=selectors.active_mask_basis();
 let expected=if j==coordinate{let a=words(pre[j]);let b=words(selectors.high[block]);core::array::from_fn(|i|reference::add_word(a[i],b[i]))}else{words(pre[j])};
 assert!((unsafe{words(AFTER[j])==expected&&NEXT==block+1}) != cfg!(NDN_invert));
}
pub(super) static mut COORD:usize=0;
pub(super) static mut LEFT:QM31=QM31::ZERO;
pub(super) static mut RIGHT:QM31=QM31::ZERO;
pub(super) static mut LOW_REPLY:QM31=QM31::ZERO;
#[cfg(NDN_active_route)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn active_route_window(){
 let selectors=Selectors{high:kani::any(),low:kani::any()};let pre:[QM31;7]=kani::any();let block:usize=kani::any();kani::assume(block<64);
 unsafe{PRE=pre;BLOCK=block;}
 let c=reference::active_coordinate(constants::ACTIVE_ROW_MASKS[block]);
 let _=selectors.active_mask_basis();
 assert!((unsafe{COORD==c&&LEFT==pre[c]&&RIGHT==selectors.high[block]})!=cfg!(NDN_invert));
}
#[cfg(NDN_active_sparse)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn active_add_window(){
 let a:QM31=kani::any();let b:QM31=kani::any();kani::assume(canon(a)&&canon(b));
 let selectors=Selectors{high:[b;64],low:[QM31::ZERO;16]};let block:usize=kani::any();let j:usize=kani::any();kani::assume(block<64&&j<7);
 unsafe{PRE=[a;7];BLOCK=block;}
 let c=reference::active_coordinate(constants::ACTIVE_ROW_MASKS[block]);let _=selectors.active_mask_basis();
 let aw=words(a);let bw=words(b);let expected=core::array::from_fn(|i|reference::active_high_word(aw[i],bw[i],j==c));
 assert!((unsafe{words(AFTER[j])==expected&&NEXT==block+1})!=cfg!(NDN_invert));
}
fn coordinate()->usize {if cfg!(NDN_coord0){0}else if cfg!(NDN_coord1){1}else if cfg!(NDN_coord2){2}else if cfg!(NDN_coord3){3}else if cfg!(NDN_coord4){4}else if cfg!(NDN_coord5){5}else{6}}
#[cfg(NDN_active_low)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn active_low_window(){
 let low:[QM31;16]=kani::any();for q in low {kani::assume(canon(q));}
 let selectors=Selectors{high:[QM31::ZERO;64],low};let c=coordinate();unsafe{COORD=c;}
 let mut expected=[0u32;4];let mut t=0usize;
 while t<reference::low_count(c){let w=words(low[reference::low_index(c,t)]);for i in 0..4 {expected[i]=reference::add_word(expected[i],w[i]);}t+=1;}
 let _=selectors.active_mask_basis();
 assert!((unsafe{words(LOW_REPLY)==expected})!=cfg!(NDN_invert));
}
pub(super) static mut PRIORS:[QM31;9]=[QM31::ZERO;9];
pub(super) static mut CALL:usize=0;
pub(super) static mut SELECTED:usize=0;
pub(super) static mut LOG_LEFT:QM31=QM31::ZERO;
pub(super) static mut LOG_RIGHT:QM31=QM31::ZERO;
pub(super) static mut LOG_REPLY:QM31=QM31::ZERO;
pub(super) fn cut_mul(x:QM31,y:QM31)->QM31{
 let n=unsafe{CALL};unsafe{CALL=n+1;}
 if n==unsafe{SELECTED}{
  let out=crate::NDE_field::qm31(x,y);
  unsafe{LOG_LEFT=x;LOG_RIGHT=y;LOG_REPLY=out;}out
 }else{unsafe{PRIORS[n]}}
}
#[cfg(NDN_residual_cut)]
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn residual_call_window(){
 let v:[QM31;10]=kani::any();for q in v {kani::assume(canon(q));}
 let prior:[QM31;9]=kani::any();for q in prior {kani::assume(canon(q));}
 let selected=if cfg!(NDN_call0){0}else if cfg!(NDN_call1){1}else if cfg!(NDN_call2){2}else if cfg!(NDN_call3){3}else if cfg!(NDN_call4){4}else if cfg!(NDN_call5){5}else if cfg!(NDN_call6){6}else if cfg!(NDN_call7){7}else{8};
 unsafe{PRIORS=prior;CALL=0;SELECTED=selected;}
 let d=[v[9].sub(v[0]),v[9].sub(v[1]),v[9].sub(v[2]),v[9].sub(v[3])];
 let (left,right)=match selected{0=>(d[0],d[1]),1=>(d[2],d[3]),2=>(v[4],d[1]),3=>(v[5],d[0]),4=>(v[6],d[3]),5=>(v[7],d[2]),6=>(v[8],prior[1]),7=>(prior[0],prior[6].add(prior[4].add(prior[5]))),_=>(prior[1],prior[2].add(prior[3]))};
 let row=CopyRowExtension{producer_values:[v[0],v[1]],consumer_values:[v[2],v[3]],producer_weights:[v[4],v[5]],consumer_weights:[v[6],v[7]]};
 let _=super::copy_residual(row,v[8],v[9]);
 let good=unsafe{CALL==9&&LOG_LEFT==left&&LOG_RIGHT==right&&LOG_REPLY==crate::NDE_field::NDE_REPLY};
 assert!(good!=cfg!(NDN_invert));
}

pub(super) trait CutMul {fn NDN_mul(self,y:Self)->Self;}
impl CutMul for QM31 {fn NDN_mul(self,y:Self)->Self{cut_mul(self,y)}}
pub(super) static mut PATTERN_GROUP:usize=0;
pub(super) static mut PATTERN_COORD:usize=0;
pub(super) static mut PATTERN_AFTER:[QM31;4]=[QM31::ZERO;4];
pub(super) static mut PATTERN_NEXT:usize=0;
#[cfg(NDN_pattern_step)]
#[kani::proof] #[kani::unwind(32)]
#[kani::stub(QM31::mul,crate::NDE_field::qm31)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn pattern_step_window(){
 let values:[QM31;4]=kani::any();let selectors:[QM31;26]=kani::any();let patterns:[QM31;POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1]=kani::any();
 let group:usize=kani::any();let coordinate:usize=kani::any();let j:usize=kani::any();kani::assume(group<4&&j<4);
 kani::assume(COPY_PATTERN_GROUP_OFFSETS[group]<=coordinate&&coordinate<COPY_PATTERN_GROUP_OFFSETS[group+1]);
 let pattern=usize::from(COPY_PATTERN_COORDINATE_PATTERNS[coordinate]);
 kani::assume(canon(values[group])&&canon(selectors[coordinate])&&canon(patterns[pattern]));
 unsafe{PATTERN_GROUP=group;PATTERN_COORD=coordinate;crate::NDE_field::NDE_COUNT=0;}
 let _=super::finish_pattern_basis_values(values,selectors,&patterns);
 let out=unsafe{PATTERN_AFTER};let product=unsafe{crate::NDE_field::NDE_REPLY};
 let a=words(values[j]);let p=words(product);let expected=core::array::from_fn(|i|reference::pattern_word(a[i],p[i],j==group));
 let good=unsafe{crate::NDE_field::NDE_COUNT==1&&crate::NDE_field::NDE_LEFT==patterns[pattern]&&crate::NDE_field::NDE_RIGHT==selectors[coordinate]&&PATTERN_NEXT==coordinate+1}&&words(out[j])==expected;
 assert!(good!=cfg!(NDN_invert));
}
