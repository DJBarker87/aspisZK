from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs';s=x[n]
s+='''
fn direct_zero<T:Copy+PartialEq>(value:T){let out=aspis_core::r0::heap::filled(0,value);let exact=matches!(out,Ok(v)if v.is_empty());assert!(exact!=cfg!(NGC_invert));}
fn direct_one<T:Copy+PartialEq>(value:T){let out=aspis_core::r0::heap::filled(1,value);let exact=match out{Ok(v)=>v.len()==1&&v[0]==value,Err(aspis_core::r0::Error::Allocation)=>true,Err(_)=>false};assert!(exact!=cfg!(NGC_invert));}
fn direct_overflow<T:Copy+PartialEq>(value:T){let out=aspis_core::r0::heap::filled(usize::MAX,value);assert!(matches!(out,Err(aspis_core::r0::Error::Allocation))!=cfg!(NGC_invert));}
fn resize_prestate<T:Copy>(len:usize,observed:usize,old:T)->Vec<T>{unsafe{let layout=alloc::alloc::Layout::array::<T>(32769).unwrap();let ptr=alloc::alloc::alloc_zeroed(layout).cast::<T>();kani::assume(!ptr.is_null());ptr.add(observed).write(old);Vec::from_raw_parts(ptr,len,32769)}}
fn resize_step<T:Copy+PartialEq>(value:T,old:T){let prefix:usize=kani::any();let j:usize=kani::any();kani::assume(prefix<=32768&&j<=prefix);let mut out=resize_prestate(prefix,j,old);let ptr=out.as_ptr();out.resize(prefix+1,value);assert!(out.len()==prefix+1&&out.as_ptr()==ptr);let want=if j<prefix{old}else{value};assert!((out[j]==want)!=cfg!(NGC_invert));}
fn clone_value<T:Copy+PartialEq>(value:T){let out=value.clone();assert!((out==value)!=cfg!(NGC_invert));}
'''
values={'u8':'kani::any::<u8>()','q':'kani::any::<K>()','raw':'kani::any::<[u64;4]>()','wide':'E::new(kani::any(),kani::any())'}
for method in ['direct_zero','direct_one','direct_overflow','resize_step','clone_value']:
 for typ,value in values.items():
  args=value+(','+value if method=='resize_step'else'')
  s+='\n#[kani::proof] KMXL\nfn '+method+'_'+typ+'(){'+method+'('+args+');}\n'
s=s.replace('KMXL','''#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]''')
x[n]=s;(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
