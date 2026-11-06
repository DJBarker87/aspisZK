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
struct NJE_CountLog { selected:u32, parent:u32, start:usize, reply:usize, calls:usize, coordinate:usize, observed:u32 }
fn NJE_group(log:&mut NJE_CountLog,level:&[u32;16],i:usize,parent:u32)->usize {
 assert_eq!(i,log.start);assert_eq!(level[i],log.selected);assert_eq!(level[log.coordinate],log.observed);assert_eq!(parent,log.parent);assert_eq!(log.calls,0);log.calls+=1;log.reply
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
 let mut log=NJE_CountLog{selected,parent,start:i,reply:j,calls:0,coordinate:k,observed:before};
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
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_count_row_exit() {
 let mut level:[u32;16]=kani::any();let n:usize=kani::any();let mut i:usize=kani::any();let mut w:usize=kani::any();let mut count:usize=kani::any();let k:usize=kani::any();
 kani::assume(n<=16&&i>=n&&k<16);let oldi=i;let oldw=w;let oldcount=count;let before=level[k];
 let mut log=NJE_CountLog{selected:kani::any(),parent:kani::any(),start:i,reply:kani::any(),calls:0,coordinate:k,observed:before};
 NJE_count_row(&mut log,&mut level,n,&mut count,&mut w,&mut i);
 if cfg!(NJE_bad_argument){count^=1;}
 assert_eq!(log.calls,0);assert_eq!(i,oldi);assert_eq!(w,oldw);assert_eq!(count,oldcount);assert_eq!(level[k],before);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_m31_chunks_active() {
 let mut state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));let at:usize=kani::any();let h:usize=kani::any();let k:usize=kani::any();
 kani::assume(at<=12&&at%4==0&&h<5&&k<16);let before=state[k];let base=state.as_mut_ptr();
 let mut iter=state[at..].chunks_exact_mut(4);let chunk=iter.next().unwrap();assert_eq!(chunk.len(),4);assert_eq!(chunk.as_mut_ptr(),unsafe{base.add(at)});
 let header:[usize;5]=unsafe{core::mem::transmute(iter)};let expected:[usize;5]=unsafe{core::mem::transmute(state[at+4..].chunks_exact_mut(4))};
 if cfg!(NJE_bad_argument){assert_eq!(header[h],expected[h]^1)}else{assert_eq!(header[h],expected[h])}
 assert_eq!(state[k],before);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_m31_chunks_exit() {
 let mut state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));let k:usize=kani::any();kani::assume(k<16);let before=state[k];
 let mut iter=state[16..].chunks_exact_mut(4);let out=iter.next();
 if cfg!(NJE_bad_argument){assert!(out.is_some())}else{assert!(out.is_none())}
 assert_eq!(state[k],before);
}

struct NJE_RowLog {reply:[u8;32],calls:usize,kind:usize,left:bool,i:usize,len:usize,ptr:*const u8,coordinate:usize,byte:usize,observed:u8}
fn NJE_row_occupied(log:&mut NJE_RowLog,val:&[[u8;32];16],i:usize)->[u8;32]{
 assert_eq!(val[log.coordinate][log.byte],log.observed);
 log.calls+=1;log.kind=1;log.i=i;log.ptr=val.as_ptr() as *const u8;log.len=16;
 log.reply
}
fn NJE_row_sibling(log:&mut NJE_RowLog,val:&[[u8;32];16],i:usize,sibling:&[u8],left:bool)->[u8;32]{
 assert_eq!(val[log.coordinate][log.byte],log.observed);
 log.calls+=1;log.kind=2;log.i=i;log.ptr=sibling.as_ptr();log.len=sibling.len();log.left=left;
 log.reply
}
fn NJE_binary_row(log:&mut NJE_RowLog,idx:&mut[u32;16],val:&mut[[u8;32];16],n:usize,nodes:&[u8],i:&mut usize,w:&mut usize,at:&mut usize)->bool{
 if *i<n {
 let parent=super::index_at(idx,*i)>>super::Arity::Two.bits();
 let digest=if *i+1<n&&super::index_at(idx,*i+1)==super::index_at(idx,*i)^1 {
 let d=NJE_row_occupied(log,val,*i);*i+=2;d
 }else{
 let Some(sibling)=nodes.get(*at..*at+32)else{return false};
 *at+=32;
 let d=NJE_row_sibling(log,val,*i,sibling,super::index_at(idx,*i)&1==0);
 *i+=1;d
 };
 idx[*w]=parent;val[*w]=digest;*w+=1;
 }
 true
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_binary_row_cut(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let nodes:[u8;96]=kani::any();
 let n:usize=kani::any();let mut i:usize=kani::any();let mut w:usize=kani::any();let mut at:usize=kani::any();let len:usize=kani::any();let k:usize=kani::any();let h:usize=kani::any();
 kani::assume(n<=16&&i<=n&&w<=i&&at<=96&&len<=96&&k<16&&h<32);
 let oldi=i;let oldw=w;let oldat=at;let beforeidx=idx[k];let beforeval=val[k][h];let parent=if i<n{idx[i]>>1}else{0};
 let left=if i<n{idx[i]&1==0}else{false};let paired=i<n&&i+1<n&&idx[i+1]==idx[i]^1;let available=at+32<=len;
 let reply:[u8;32]=kani::any();let expectedreply=reply[h];let base=nodes.as_ptr();let valuebase=val.as_ptr() as *const u8;
 let mut log=NJE_RowLog{reply,calls:0,kind:0,left:false,i:0,len:0,ptr:core::ptr::null(),coordinate:k,byte:h,observed:beforeval};
 let succeeded=NJE_binary_row(&mut log,&mut idx,&mut val,n,&nodes[..len],&mut i,&mut w,&mut at);
 macro_rules! assert_eq {($a:expr,$b:expr)=>{assert!(if cfg!(NJE_bad_argument){$a!=$b}else{$a==$b})}}
 // Each configuration selects one independent assertion family on the SAME native step.
 let theorem:usize=if cfg!(NJE_row_0){0}else if cfg!(NJE_row_1){1}else if cfg!(NJE_row_2){2}else if cfg!(NJE_row_3){3}else if cfg!(NJE_row_4){4}else if cfg!(NJE_row_5){5}else if cfg!(NJE_row_6){6}else if cfg!(NJE_row_7){7}else if cfg!(NJE_row_8){8}else if cfg!(NJE_row_9){9}else if cfg!(NJE_row_10){10}else{11};
 if theorem==0 {assert_eq!(succeeded,oldi>=n||paired||available)}
 if theorem==1 {assert_eq!(log.calls,usize::from(oldi<n&&(paired||available)))}
 if theorem==2 {if oldi<n&&paired {assert_eq!(log.kind,1);assert_eq!(log.i,oldi);assert_eq!(log.ptr,valuebase);assert_eq!(log.len,16)}}
 if theorem==3 {if oldi<n&&!paired&&available {assert_eq!(log.kind,2);assert_eq!(log.i,oldi);assert_eq!(log.ptr,unsafe{base.add(oldat)});assert_eq!(log.len,32)}}
 if theorem==4 {if oldi<n&&!paired&&available {assert_eq!(log.left,left)}}
 if theorem==5 {assert_eq!(i,if oldi<n&&paired{oldi+2}else if oldi<n&&available{oldi+1}else{oldi})}
 if theorem==6 {assert_eq!(w,if oldi<n&&(paired||available){oldw+1}else{oldw})}
 if theorem==7 {assert_eq!(at,if oldi<n&&!paired&&available{oldat+32}else{oldat})}
 if theorem==8 {assert_eq!(idx[k],if oldi<n&&(paired||available)&&k==oldw{parent}else{beforeidx})}
 if theorem==9 {assert_eq!(val[k][h],if oldi<n&&(paired||available)&&k==oldw{expectedreply}else{beforeval})}
 if theorem==10 {if oldi<n&&!paired&&!available{assert!(!succeeded);assert_eq!(log.calls,0);assert_eq!(i,oldi);assert_eq!(w,oldw);assert_eq!(at,oldat);assert_eq!(idx[k],beforeidx);assert_eq!(val[k][h],beforeval)}}
 if theorem==11 {if oldi==n{assert!(succeeded);assert_eq!(log.calls,0);assert_eq!(i,oldi);assert_eq!(w,oldw);assert_eq!(at,oldat);assert_eq!(idx[k],beforeidx);assert_eq!(val[k][h],beforeval)}}

}
