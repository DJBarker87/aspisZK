"""Resume same-name native properties; controls change one asserted equality."""
from NEH_extra import *

def remember(rp,pos,neg):
 p=E/'NEH_NEW_CONTROL_PAIRS.json';pairs=read_json(p) if p.exists() else []
 item=dict(original_receipt=rp,positive=pos,control=neg)
 if item not in pairs:pairs.append(item)
 p.write_text(json.dumps(pairs,indent=2)+'\n')

def nbg():
 # These four complete original modules are already static-free. No field
 # multiplication or global logging is reached by these selected functions.
 n='crates/aspis-core/src/field/NBG_runtime.rs'
 tasks=[(7,'assert!(a.a.0==add(x.a.0,y.a.0) && a.b.0==add(x.b.0,y.b.0));'),(6,'assert!(x.add(y).0==add(x.0,y.0));'),(8,'assert!(a.c0.a.0==add(x.c0.a.0,y.c0.a.0) && a.c0.b.0==add(x.c0.b.0,y.c0.b.0));'),(12,'assert!(c.a.0==a.0 && c.b.0==b.0);')]
 for i,(num,assertion) in enumerate(tasks):
  rp=f'evidence/native-tx2c-20261027/NBG_K{num:03}/receipt.json';patch=ROOT/Path(rp).parent.parent/(f'NBG_K{num:03}-harness.patch');o=dict(patched_files(patch.read_text()));assert n in o
  assert assertion in o[n]
  for neg in [False,True]:
   a=f'NEH_K{76+2*i+int(neg):03}'
   if (E/a/'receipt.json').exists():continue
   changed=dict(o)
   if neg:changed[n]=o[n].replace(assertion,'assert!(!('+assertion[len('assert!('):-2]+'));',1)
   publish(a,rp,changed,neg)
  remember(rp,f'NEH_K{76+2*i:03}',f'NEH_K{77+2*i:03}')
if __name__=='__main__':nbg()

def nbq(start=84):
 p='crates/aspis-r1-cost-probe/src/fast_pairing.rs';src=dict(patched_files((ROOT/'evidence/native-tx2h-20261028/NBQ_K001-harness.patch').read_text()))[p]
 startmod=src.index('    #[cfg(kani)]\n    mod NBQ_private');brace=src.index('{',startmod);depth=1;i=brace+1
 while depth:
  if src[i]=='{':depth+=1
  if src[i]=='}':depth-=1
  i+=1
 module=src[startmod:i]
 for j,(num,name,assertion) in enumerate([(1,'reduce_all','assert!(u64::from(r)==x%u64::from(P));'),(2,'new','assert!(d.sums==[0;4]);')]):
  rp=f'evidence/native-tx2h-20261028/NBQ_K{num:03}/receipt.json'
  for neg in [False,True]:
   a=f'NEH_K{start+2*j+int(neg):03}'
   if (E/a/'receipt.json').exists():continue
   b=module
   if neg:b=b.replace(assertion,'assert!(!('+assertion[len('assert!('):-2]+'));',1)
   b=b.replace('#[kani::proof]', '#[kani::proof] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NEH_kmx::KMX_copy_nonoverlapping)]')
   raw=frozen(p).decode();# Insert at the original canonical module's closing brace.
   # Original patch retained exact context before canonical's final brace.
   marker='\n}\n\n\n///'
   # Locate canonical braces structurally; preserve every original source byte.
   at=raw.index('{',raw.index('mod canonical'));d=1;k=at+1
   while d:
    if raw[k]=='{':d+=1
    if raw[k]=='}':d-=1
    k+=1
   raw=raw[:k-1]+b+'\n'+raw[k-1:]
   o=root_overlay('crates/aspis-r1-cost-probe','NEH_kmx','extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));');o[p]=raw
   publish(a,rp,o,neg)
  remember(rp,f'NEH_K{start+2*j:03}',f'NEH_K{start+2*j+1:03}')
