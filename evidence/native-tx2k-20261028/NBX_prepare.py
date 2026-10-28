from pathlib import Path
import re,json,importlib.util,sys
E=Path(__file__).resolve().parent
# Construct arbitrary full typed inputs, not validated fixtures.
src=Path('crates/aspis-statement/src/pool_v1/verifier_registry.rs').read_text()
out='#![allow(non_snake_case,unused_variables)]\nuse super::*;\n'
for t in ['VerifierRegistryV1','VerifierRegistryV2','VerifierRegistryEntryV1','VerifierRegistryEntryV2']:
 fields=re.findall(r'pub (\w+): ([^,\n]+),',re.search(r'pub struct '+t+r' \{(.*?)\n\}',src,re.S).group(1))
 out+='fn NBX_any_'+t+'()->'+t+'{'+t+'{'+','.join(n+':'+('NBX_status()' if ty=='VerifierEntryStatusV1' else 'kani::any()') for n,ty in fields)+'}}\n'
out+='fn NBX_status()->VerifierEntryStatusV1 {match kani::any::<u8>() {0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}}\n'
attrs='''#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
#[kani::unwind(33)]
'''
items=[]
def harness(name,body,condition):
 global out
 for neg in [False,True]:
  n=name+('_negative' if neg else '')
  out+=attrs+'fn NBX_'+n+'(){'+body+'\nassert!('+('!(' if neg else '(')+condition+'));}\n'
  items.append(('pool_v1::verifier_registry::NBX_slots::NBX_'+n,neg))
for op,t,method,expr in [(25,'VerifierRegistryV1','is_paused','r.flags & 1 != 0'),(26,'VerifierRegistryV1','is_immutable','r.flags & 2 != 0'),(27,'VerifierRegistryV2','is_paused','r.flags & 1 != 0'),(28,'VerifierRegistryV2','is_immutable','r.flags & 2 != 0'),(29,'VerifierRegistryEntryV2','is_active_at','r.status==VerifierEntryStatusV1::Active && r.activation_slot<=slot && (r.retirement_slot==u64::MAX || slot<r.retirement_slot)'),(30,'VerifierRegistryEntryV1','is_active_at','r.status==VerifierEntryStatusV1::Active && r.activation_slot<=slot && (r.retirement_slot==u64::MAX || slot<r.retirement_slot)')]:
 body=f'let r=NBX_any_{t}();let slot:u64=kani::any();let ambient:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<32);let before=ambient[j];let input=r.pool[j];let got=r.{method}('+('slot' if op in [29,30] else '')+');'
 harness('op'+str(op),body,f'got==({expr}) && ambient[j]==before && r.pool[j]==input')
for t in ['VerifierRegistryEntryV1','VerifierRegistryEntryV2']:
 harness('retirement_'+t,'let r=NBX_any_'+t+'();let got=r.has_no_retirement_slot();','got==(r.retirement_slot==u64::MAX)')
harness('status','let v:u8=kani::any();let got=VerifierEntryStatusV1::try_from(v);','match got {Ok(s)=>v<4 && s as u8==v,Err(e)=>v>=4 && e==PoolV1VerifierRegistryFormatError::InvalidStatus}')
harness('binding','let a:[u8;32]=kani::any();let got=required_binding_is_zero(&a);','got==(a==[0;32])')
(E/'NBX_slots.rs.txt').write_text(out)
(E/'NBX_SEQUENCE.json').write_text(json.dumps(items,indent=2)+'\n')
sys.argv=['prepare','none'];sp=importlib.util.spec_from_file_location('nbx',E/'NBX_native.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
m.admit('NBX_SETUP')
r=m.py(f'''from pathlib import Path
import json,hashlib
b=Path({m.B!r});s=b/'NBU_src';p=s/'crates/aspis-statement/src/pool_v1/NBX_slots.rs';assert not p.exists();p.write_text({out!r})
p=s/'crates/aspis-statement/src/pool_v1/verifier_registry.rs';p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path = "NBX_slots.rs"]\\nmod NBX_slots;\\n')
cache=Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028')
pins={{str(p.relative_to(cache)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}}
(b/'NBX_CACHE_IMPORTED.json').write_text(json.dumps(pins,indent=2));print(json.dumps(dict(cache_files=len(pins),pins=pins)))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBX_CACHE_IMPORTED.json').write_text(r.stdout)
