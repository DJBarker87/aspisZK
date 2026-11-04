"""Frozen source-fission windows; no repository shipped source is written."""
from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent
frozen=lambda n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
P=E.parent/'slice-d-check-20261104'
x={};pins=json.loads((P/'NFU_SOURCE_PINS.json').read_text());patch=[]
for n in json.loads((P/'NFU_NATIVE_INPUTS.json').read_text()):
 if '/NFU_' not in n:x[n]=frozen(n)
C='crates/aspis-core/src/'
x[C+'lib.rs']=frozen(C+'lib.rs').replace('#![no_std]','#![cfg_attr(kani,feature(allocator_api))]\n#![no_std]',1)
s=frozen(C+'field.rs')
for typ in ['M31','CM31','QM31']:
 s=s.replace('pub struct '+typ, '#[cfg_attr(kani,derive(kani::Arbitrary))]\npub struct '+typ,1)
x[C+'field.rs']=s
V='crates/aspis-r1-cost-probe/src/'
x[V+'verifier.rs']+='\n#[cfg(kani)]\n#[path="NGC_windows.rs"]\nmod NGC_windows;\n'
x[V+'NGC_windows.rs']='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct HeapLog{n:usize,value:K,reserve:bool,stage:u8}
fn reserve(out:&mut Vec<K>,n:usize,log:&mut HeapLog)->Result<(),()>{assert!(out.is_empty());assert!(log.stage==0);log.n=n;log.stage=1;if log.reserve{Ok(())}else{Err(())}}
fn resize(out:&mut Vec<K>,n:usize,value:K,log:&mut HeapLog,reply:Vec<K>){assert!(log.stage==1);assert!(n==log.n);log.value=value;log.stage=2;*out=reply;}
// Exact helper body after substituting the two std-call interfaces. The library
// replies are owned by this SAME local record; no allocator success is assumed.
fn filled_window(n:usize,value:K,log:&mut HeapLog,reply:Vec<K>)->Result<Vec<K>,aspis_core::r0::Error>{
 let mut out=Vec::new();
 reserve(&mut out,n,log).map_err(|_|aspis_core::r0::Error::Allocation)?;
 resize(&mut out,n,value,log,reply);
 Ok(out)
}
struct NewLog{n:usize,value:K,count:u8,success:bool}
fn filled_child(n:usize,value:K,log:&mut NewLog,reply:Vec<K>)->Result<Vec<K>,aspis_core::r0::Error>{log.n=n;log.value=value;log.count+=1;if log.success{Ok(reply)}else{Err(aspis_core::r0::Error::Allocation)}}
fn new_window(v:Variant,log:&mut NewLog,reply:Vec<K>)->Result<Accumulator,Error>{Ok(Accumulator{weights:filled_child(v.final_len(),K::ZERO,log,reply).map_err(|_|Error::Allocation)?,rhs:E::ZERO,power:K::ONE,next:0})}
fn arbitrary_vec()->Vec<K>{Vec::from(kani::any::<[K;64]>())}
#[kani::proof] KMXL
fn heap_schedule(){let n:usize=kani::any();let value:K=kani::any();let reserve:bool=kani::any();let reply=arbitrary_vec();let ptr=reply.as_ptr();let mut log=HeapLog{n:0,value:K::ONE,reserve,stage:0};let out=filled_window(n,value,&mut log,reply);let exact=if reserve{match out{Ok(v)=>log.stage==2&&log.n==n&&log.value==value&&v.len()==64&&v.as_ptr()==ptr,Err(_)=>false}}else{matches!(out,Err(aspis_core::r0::Error::Allocation))&&log.stage==1&&log.n==n};assert!(exact!=cfg!(NGC_invert));}
#[kani::proof] KMXL
fn new_schedule(){let tag:u8=kani::any();kani::assume(tag<3);let v=match tag{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};let success:bool=kani::any();let reply=arbitrary_vec();let ptr=reply.as_ptr();let mut log=NewLog{n:0,value:K::ONE,count:0,success};let out=new_window(v,&mut log,reply);assert!(log.count==1&&log.n==if tag==0{256}else{64}&&log.value==K::ZERO);let exact=if success{match out{Ok(a)=>a.weights.len()==64&&a.weights.as_ptr()==ptr&&a.rhs==E::ZERO&&a.power==K::ONE&&a.next==0,Err(_)=>false}}else{matches!(out,Err(Error::Allocation))};assert!(exact!=cfg!(NGC_invert));}
#[kani::proof] KMXL
fn vector_copy_positive(){let src:[K;64]=kani::any();let i:usize=kani::any();kani::assume(i<64);let expected=src[i];let dst=Vec::from(src);assert!(dst.len()==64&&dst[i]==expected);}
#[kani::proof] KMXL
fn vector_copy_negative(){let src:[K;64]=kani::any();let i:usize=kani::any();kani::assume(i<64);let expected=src[i];let dst=Vec::from(src);assert!(dst.len()!=64||dst[i]!=expected);}
'''.replace('KMXL','''#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]''')
for n,s in x.items():
 pins[n]=hashlib.sha256(s.encode()).hexdigest()
 old=''if '/NGC_'in n else frozen(n)
 patch+=difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n)
(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');(E/'NGC_HARNESSES.patch').write_text(''.join(patch))
