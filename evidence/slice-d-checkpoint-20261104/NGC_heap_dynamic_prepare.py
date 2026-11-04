from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs';s=x[n]
s=s.replace('struct HeapLog{n:usize,value:K,','struct HeapLog<T>{n:usize,value:T,')
s=s.replace('fn reserve(out:&mut Vec<K>,n:usize,log:&mut HeapLog)', 'fn reserve<T>(out:&mut Vec<T>,n:usize,log:&mut HeapLog<T>)')
s=s.replace('fn resize(out:&mut Vec<K>,n:usize,value:K,log:&mut HeapLog,reply:Vec<K>)','fn resize<T>(out:&mut Vec<T>,n:usize,value:T,log:&mut HeapLog<T>,reply:Vec<T>)')
s=s.replace('fn filled_window(n:usize,value:K,log:&mut HeapLog,reply:Vec<K>)->Result<Vec<K>,aspis_core::r0::Error>', 'fn filled_window<T:Copy>(n:usize,value:T,log:&mut HeapLog<T>,reply:Vec<T>)->Result<Vec<T>,aspis_core::r0::Error>')
start=s.index('fn heap_schedule(){');end=s.index('\n#[kani::proof]',start)
s=s[:start]+'''fn heap_schedule(){heap_check(kani::any::<K>(),kani::any::<K>());}
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
#[kani::proof] KMXL
fn heap_u8(){heap_check(kani::any::<u8>(),kani::any::<u8>());}
#[kani::proof] KMXL
fn heap_raw(){heap_check(kani::any::<[u64;4]>(),kani::any::<[u64;4]>());}
#[kani::proof] KMXL
fn heap_wide(){heap_check(E::new(kani::any(),kani::any()),E::new(kani::any(),kani::any()));}
#[kani::proof] KMXL
fn heap_payload_positive(){let n:usize=kani::any();let i:usize=kani::any();kani::assume(n>0&&n<=32768&&i<n);let payload:K=kani::any();let out=oracle_vec(n,payload,i);assert!(out.len()==n&&out[i]==payload);}
#[kani::proof] KMXL
fn heap_payload_negative(){let n:usize=kani::any();let i:usize=kani::any();kani::assume(n>0&&n<=32768&&i<n);let payload:K=kani::any();let out=oracle_vec(n,payload,i);assert!(out.len()!=n||out[i]!=payload);}
''' +s[end:]
s=s.replace('KMXL','''#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]''')
x[n]=s;(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
