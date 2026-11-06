use aspis_core::field::M31;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_iter_mut_active() {
 let mut state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));
 let at:usize=kani::any();let k:usize=kani::any();let h:usize=kani::any();let reply=M31(kani::any());
 kani::assume(at<16&&k<16&&h<2);
 let base=state.as_mut_ptr();let before=state[k];let selected=state[at];
 let mut iter=state[at..].iter_mut();let value=iter.next().unwrap();
 let address=value as *mut M31;let observed=*value;*value=reply;
 let header:[usize;2]=unsafe{core::mem::transmute(iter)};
 let expected:[usize;2]=unsafe{core::mem::transmute(state[at+1..].iter_mut())};
 if cfg!(NJE_bad_argument){assert_eq!(header[h],expected[h]^1)}else{assert_eq!(header[h],expected[h])}
 assert_eq!(address,unsafe{base.add(at)});assert_eq!(observed,selected);
 assert_eq!(state[k],if k==at{reply}else{before});
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_iter_mut_exit() {
 let mut state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));
 let k:usize=kani::any();kani::assume(k<16);let before=state[k];
 let mut iter=state[16..].iter_mut();let out=iter.next();
 if cfg!(NJE_bad_argument){assert!(out.is_some())}else{assert!(out.is_none())}
 assert_eq!(state[k],before);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_internal_sum_iter() {
 let state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));
 let at:usize=kani::any();let mut sum:u64=kani::any();let h:usize=kani::any();
 kani::assume(1<=at&&at<16&&h<2&&sum<=(at as u64-1)*2147483647&&state[at].0<2147483647);
 let before=sum;let mut iter=state[at..].iter().map(|value|value.0 as u64);
 let value=iter.next().unwrap();sum+=value;
 let header:[usize;2]=unsafe{core::mem::transmute(iter)};
 let expected:[usize;2]=unsafe{core::mem::transmute(state[at+1..].iter().map(|value|value.0 as u64))};
 if cfg!(NJE_bad_argument){sum^=1;}
 assert_eq!(value,state[at].0 as u64);assert_eq!(sum,before+state[at].0 as u64);
 assert!(sum<=at as u64*2147483647);assert_eq!(header[h],expected[h]);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_internal_sum_exit() {
 let state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));
 let mut iter=state[16..].iter().map(|value|value.0 as u64);let out=iter.next();
 if cfg!(NJE_bad_argument){assert!(out.is_some())}else{assert!(out.is_none())}
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_external_sum_map() {
 let state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));
 let row:usize=kani::any();let column:usize=kani::any();let mut sum:u64=kani::any();
 kani::assume(row<4&&column<4&&sum<=row as u64*2147483647&&state[row*4+column].0<2147483647);
 let before=sum;let mut iter=(row..4).map(|row|state[row*4+column].0 as u64);
 let value=iter.next().unwrap();sum+=value;
 if cfg!(NJE_bad_argument){sum^=1;}
 assert_eq!(value,state[row*4+column].0 as u64);assert_eq!(sum,before+value);
 assert!(sum<=(row as u64+1)*2147483647);assert_eq!(iter.size_hint(),(3-row,Some(3-row)));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_external_columns_control() {
 let mut positions=[0usize;4];let mut len=0usize;
 let _: [u64;4]=core::array::from_fn(|column|{positions[len]=column;len+=1;0});
 if cfg!(NJE_bad_argument){positions[2]^=1;}
 assert_eq!(len,4);let i:usize=kani::any();kani::assume(i<4);assert_eq!(positions[i],i);
}
struct NJE_WellLog { pointer:*const u32, length:usize, calls:usize, order:bool, domain:bool }
fn NJE_order_all(log:&mut NJE_WellLog,indices:&[u32])->bool {
 assert_eq!(indices.as_ptr(),log.pointer);assert_eq!(indices.len(),log.length);assert_eq!(log.calls,0);log.calls+=1;log.order
}
fn NJE_domain_all(log:&mut NJE_WellLog,indices:&[u32])->bool {
 assert_eq!(indices.as_ptr(),log.pointer);assert_eq!(indices.len(),log.length);assert_eq!(log.calls,1);log.calls+=1;log.domain
}
// Exact frozen wrapper with only the two all-expression boundaries logged.
fn NJE_well_wrapper(log:&mut NJE_WellLog,indices:&[u32])->bool {
 !indices.is_empty()
  && indices.len() <= super::MAX_BATCH
  && NJE_order_all(log,indices)
  && NJE_domain_all(log,indices)
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_well_entry_cut() {
 let values:[u32;17]=kani::any();let n:usize=kani::any();let k:usize=kani::any();
 kani::assume(n<=17&&k<17);let before=values[k];let indices=&values[..n];
 let ordered:bool=kani::any();let domain:bool=kani::any();
 let mut log=NJE_WellLog{pointer:indices.as_ptr(),length:n,calls:0,order:ordered,domain};
 if cfg!(NJE_bad_argument){log.length^=1;}
 let out=NJE_well_wrapper(&mut log,indices);let valid=0<n&&n<=16;
 assert_eq!(out,valid&&ordered&&domain);
 assert_eq!(log.calls,if !valid{0}else if ordered{2}else{1});assert_eq!(values[k],before);
}
struct NJE_CountLog { selected:u32, parent:u32, start:usize, reply:usize, calls:usize }
fn NJE_group(log:&mut NJE_CountLog,level:&[u32;16],i:usize,parent:u32)->usize {
 assert_eq!(i,log.start);assert_eq!(level[i],log.selected);assert_eq!(parent,log.parent);assert_eq!(log.calls,0);log.calls+=1;log.reply
}
fn NJE_count_row(log:&mut NJE_CountLog,level:&mut[u32;16],n:usize,count:&mut usize,w:&mut usize,i:&mut usize) {
 if *i<n {
  let parent=super::index_at(level,*i)>>super::Arity::Two.bits();
  let j=NJE_group(log,level,*i,parent);
  *count+=super::Arity::Two.width()-(j-*i);
  level[*w]=parent;*w+=1;*i=j;
 }
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_count_row_cut() {
 let mut level:[u32;16]=kani::any();let n:usize=kani::any();let mut i:usize=kani::any();let mut w:usize=kani::any();let mut count:usize=kani::any();let delta:usize=kani::any();let k:usize=kani::any();
 kani::assume(n<=16&&i<n&&w<=i&&count<=576&&1<=delta&&delta<=2&&i+delta<=n&&k<16);
 let oldi=i;let oldw=w;let oldcount=count;let before=level[k];let selected=level[i];let parent=selected>>1;let j=i+delta;
 let mut log=NJE_CountLog{selected,parent,start:i,reply:j,calls:0};
 if cfg!(NJE_bad_argument){log.parent^=1;}
 NJE_count_row(&mut log,&mut level,n,&mut count,&mut w,&mut i);
 assert_eq!(log.calls,1);assert_eq!(i,j);assert_eq!(w,oldw+1);assert_eq!(count,oldcount+2-delta);
 assert_eq!(level[k],if k==oldw{parent}else{before});assert!(w<=i&&oldi<i&&i<=n);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_count_levels_control() {
 let mut rounds=[0u32;18];let mut len=0usize;
 for height in 0..super::Arity::Two.levels(){rounds[len]=height;len+=1;}
 if cfg!(NJE_bad_argument){rounds[0]^=1;}
 let k:usize=kani::any();kani::assume(k<18);assert_eq!(len,18);assert_eq!(rounds[k],k as u32);
}
