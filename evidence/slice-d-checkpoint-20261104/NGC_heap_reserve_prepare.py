from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs';s=x[n]
s+='''
// Exact initial reserve prefix, with real std allocation and both Results.
fn reserve_prefix<T:Copy>(){let n:usize=kani::any();kani::assume(n<=32768);let mut out=Vec::<T>::new();let result=out.try_reserve_exact(n);let exact=out.is_empty()&&match result{Ok(())=>out.capacity()>=n,Err(_)=>out.capacity()==0};assert!(exact!=cfg!(NGC_invert));}
fn reject_filled<T:Copy>(n:usize,_value:T)->Result<Vec<T>,aspis_core::r0::Error>{assert!(n==64);Err(aspis_core::r0::Error::Allocation)}
#[kani::proof] KMXL
#[kani::stub(aspis_core::r0::heap::filled,reject_filled)]
fn new_allocation_error(){let result=Accumulator::new(Variant::S2);assert!(matches!(result,Err(Error::Allocation))!=cfg!(NGC_invert));}
'''
for typ,T in [('u8','u8'),('q','K'),('raw','[u64;4]'),('wide','E')]:
 s+='\n#[kani::proof] KMXL\nfn reserve_prefix_'+typ+'(){reserve_prefix::<'+T+'>();}\n'
s=s.replace('KMXL','''#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]''')
x[n]=s;(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
