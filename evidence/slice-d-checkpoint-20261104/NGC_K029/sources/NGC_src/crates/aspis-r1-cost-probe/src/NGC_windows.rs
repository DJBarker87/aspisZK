use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct HeapLog<T>{n:usize,value:T,reserve:bool,stage:u8}
fn reserve<T>(out:&mut Vec<T>,n:usize,log:&mut HeapLog<T>)->Result<(),()>{assert!(out.is_empty());assert!(log.stage==0);log.n=n;log.stage=1;if log.reserve{Ok(())}else{Err(())}}
fn resize<T>(out:&mut Vec<T>,n:usize,value:T,log:&mut HeapLog<T>,reply:Vec<T>){assert!(log.stage==1);assert!(n==log.n);log.value=value;log.stage=2;*out=reply;}
// Exact helper body after substituting the two std-call interfaces. The library
// replies are owned by this SAME local record; no allocator success is assumed.
fn filled_window<T:Copy>(n:usize,value:T,log:&mut HeapLog<T>,reply:Vec<T>)->Result<Vec<T>,aspis_core::r0::Error>{
 let mut out=Vec::new();
 reserve(&mut out,n,log).map_err(|_|aspis_core::r0::Error::Allocation)?;
 resize(&mut out,n,value,log,reply);
 Ok(out)
}
struct NewLog{n:usize,value:K,count:u8,success:bool}
fn filled_child(n:usize,value:K,log:&mut NewLog,reply:Vec<K>)->Result<Vec<K>,aspis_core::r0::Error>{log.n=n;log.value=value;log.count+=1;if log.success{Ok(reply)}else{Err(aspis_core::r0::Error::Allocation)}}
fn new_window(v:Variant,log:&mut NewLog,reply:Vec<K>)->Result<Accumulator,Error>{Ok(Accumulator{weights:filled_child(v.final_len(),K::ZERO,log,reply).map_err(|_|Error::Allocation)?,rhs:E::ZERO,power:K::ONE,next:0})}
fn arbitrary_vec()->Vec<K>{Vec::from(kani::any::<[K;64]>())}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn heap_schedule(){heap_check(kani::any::<K>(),kani::any::<K>());}
// Only instantiated at frozen zero-valid field/integer/array types. Successful
// allocation is part of the physical interpretation, independent of the
// reserve outcome supplied to the observed helper. No whole-buffer loop.
fn oracle_vec<T:Copy>(n:usize,payload:T,index:usize)->Vec<T>{
 if n==0{return Vec::new();}
 unsafe{let layout=alloc::alloc::Layout::array::<T>(n).unwrap();let ptr=alloc::alloc::alloc_zeroed(layout).cast::<T>();kani::assume(!ptr.is_null());ptr.add(index).write(payload);Vec::from_raw_parts(ptr,n,n)}
}
fn heap_check<T:Copy+PartialEq>(value:T,payload:T){
 let n:usize=kani::any();let index:usize=kani::any();kani::assume(n<=32768);if n>0{kani::assume(index<n);}else{kani::assume(index==0);}
 let reply=oracle_vec(n,payload,index);let ptr=reply.as_ptr();let reserve:bool=kani::any();let mut log=HeapLog{n:0,value,reserve,stage:0};let out=filled_window(n,value,&mut log,reply);
 let exact=if reserve{match out{Ok(v)=>log.stage==2&&log.n==n&&log.value==value&&v.len()==n&&v.as_ptr()==ptr&&(n==0||v[index]==payload),Err(_)=>false}}else{matches!(out,Err(aspis_core::r0::Error::Allocation))&&log.stage==1&&log.n==n};assert!(exact!=cfg!(NGC_invert));
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn heap_u8(){heap_check(kani::any::<u8>(),kani::any::<u8>());}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn heap_raw(){heap_check(kani::any::<[u64;4]>(),kani::any::<[u64;4]>());}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn heap_wide(){heap_check(E::new(kani::any(),kani::any()),E::new(kani::any(),kani::any()));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn heap_payload_positive(){let n:usize=kani::any();let i:usize=kani::any();kani::assume(n>0&&n<=32768&&i<n);let payload:K=kani::any();let out=oracle_vec(n,payload,i);assert!(out.len()==n&&out[i]==payload);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn heap_payload_negative(){let n:usize=kani::any();let i:usize=kani::any();kani::assume(n>0&&n<=32768&&i<n);let payload:K=kani::any();let out=oracle_vec(n,payload,i);assert!(out.len()!=n||out[i]!=payload);}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn new_schedule(){let tag:u8=kani::any();kani::assume(tag<3);let v=match tag{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};let success:bool=kani::any();let reply=arbitrary_vec();let ptr=reply.as_ptr();let mut log=NewLog{n:0,value:K::ONE,count:0,success};let out=new_window(v,&mut log,reply);assert!(log.count==1&&log.n==if tag==0{256}else{64}&&log.value==K::ZERO);let exact=if success{match out{Ok(a)=>a.weights.len()==64&&a.weights.as_ptr()==ptr&&a.rhs==E::ZERO&&a.power==K::ONE&&a.next==0,Err(_)=>false}}else{matches!(out,Err(Error::Allocation))};assert!(exact!=cfg!(NGC_invert));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn vector_copy_positive(){let src:[K;64]=kani::any();let i:usize=kani::any();kani::assume(i<64);let expected=src[i];let dst=Vec::from(src);assert!(dst.len()==64&&dst[i]==expected);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn vector_copy_negative(){let src:[K;64]=kani::any();let i:usize=kani::any();kani::assume(i<64);let expected=src[i];let dst=Vec::from(src);assert!(dst.len()!=64||dst[i]!=expected);}

fn qword(q:K,j:usize)->u32{match j{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
// One actual enumerate/iter_mut transition, at an arbitrary cursor/prestate.
fn finish_window(b:&BatchedWeights,weights:&mut[K],index:usize)->usize{
 let mut iter=weights.iter_mut().enumerate();
 let (i,w)=iter.nth(index).unwrap();*w=b.value(i);iter.len()
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn finish_step(){let raw:[[u64;4];64]=kani::any();let b=BatchedWeights{raw:Vec::from(raw),terms:kani::any()};let mut old:[K;64]=kani::any();let index:usize=kani::any();let observed:usize=kani::any();let limb:usize=kani::any();kani::assume(index<64&&observed<64&&limb<4);let previous=old[observed];let rawword=raw[index][limb];let left=finish_window(&b,&mut old,index);assert!(left==63-index);let expected=if observed==index{M31::reduce_u64(rawword).0}else{qword(previous,limb)};assert!(qword(old[observed],limb)==if cfg!(NGC_invert){expected^1}else{expected});}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn finish_canonical(){let raw:[[u64;4];64]=kani::any();let b=BatchedWeights{raw:Vec::from(raw),terms:kani::any()};let index:usize=kani::any();let limb:usize=kani::any();kani::assume(index<64&&limb<4);let got=b.value(index);assert!((qword(got,limb)<2147483647)!=cfg!(NGC_invert));}
struct FinishControl{count:usize,selected:usize,index:usize,place:*mut K}
fn finish_control(weights:&mut[K],log:&mut FinishControl){for(i,w)in weights.iter_mut().enumerate(){if log.count==log.selected{log.index=i;log.place=w as *mut K;}log.count+=1;}}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn finish_order(){let mut weights:[K;64]=kani::any();let selected:usize=kani::any();kani::assume(selected<64);let mut log=FinishControl{count:0,selected,index:99,place:core::ptr::null_mut()};finish_control(&mut weights,&mut log);let exact=log.count==64&&log.index==selected&&log.place==unsafe{weights.as_mut_ptr().add(selected)};assert!(exact!=cfg!(NGC_invert));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_copy_positive(){let raw:[[u64;4];64]=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<64&&j<4);let expected=raw[i][j];let out=Vec::from(raw);assert!(out.len()==64&&out[i][j]==expected);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_copy_negative(){let raw:[[u64;4];64]=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<64&&j<4);let expected=raw[i][j];let out=Vec::from(raw);assert!(out.len()!=64||out[i][j]!=expected);}
