"""Pin exact compiled module bytes and export the own cumulative scratch patch."""
from pathlib import Path
import json,hashlib,subprocess,re,difflib
E=Path(__file__).resolve().parent
versions={}
for p in E.glob('NCC_*.rs.txt'):versions.setdefault(hashlib.sha256(p.read_bytes()).hexdigest(),[]).append(p.name)
rows=[]
for p in sorted(E.glob('NCC_K*/receipt.json')):
 r=json.loads(p.read_text());h=r['source_hashes']['NBU_src/crates/aspis-statement/src/pool_v1/NCC_slots.rs'];assert h in versions,(r['attempt'],h)
 rows.append(dict(attempt=r['attempt'],harness=r['module'],source_sha256=h,complete_local_snapshots=versions[h]))
(E/'NCC_SOURCE_VERSIONS.json').write_text(json.dumps(rows,indent=2)+'\n')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';n='crates/aspis-statement/src/pool_v1/verifier_registry.rs'
frozen=subprocess.check_output(['git','show',rev+':'+n],text=True)
nbx='\n#[cfg(kani)]\n#[path = "NBX_slots.rs"]\nmod NBX_slots;\n';ncc='\n#[cfg(kani)]\n#[path = "NCC_slots.rs"]\nmod NCC_slots;\n'
base=frozen+nbx;new=frozen
for t in ['VerifierRegistryV1','VerifierRegistryV2','VerifierRegistryEntryV1','VerifierRegistryEntryV2']:
 m=re.search(r'(impl '+t+r' \{)(.*?)(\n\})',new,re.S);block=m[2]
 if 'Entry' in t:
  text='    #[cfg_attr(kani, kani::requires(true))]\n    #[cfg_attr(kani, kani::ensures(|result: &bool| *result == (self.status == VerifierEntryStatusV1::Active && self.activation_slot <= slot && (self.retirement_slot == u64::MAX || slot < self.retirement_slot))))]\n'
  block=block.replace('    pub fn is_active_at',text+'    pub fn is_active_at')
 else:
  for method,mask in [('is_paused',1),('is_immutable',2)]:
   text=f'    #[cfg_attr(kani, kani::requires(true))]\n    #[cfg_attr(kani, kani::ensures(|result: &bool| *result == (self.flags & {mask} != 0)))]\n';block=block.replace('    pub fn '+method,text+'    pub fn '+method)
 new=new[:m.start(2)]+block+new[m.end(2):]
new+=nbx+ncc
installed=json.loads((E/'NCC_CONTRACT_INSTALL.json').read_text());assert hashlib.sha256(new.encode()).hexdigest()==installed['after'];assert hashlib.sha256((frozen+nbx+ncc).encode()).hexdigest()==installed['non_annotation_source_sha256']
patch=''.join(difflib.unified_diff(base.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
n='crates/aspis-statement/src/pool_v1/NCC_slots.rs';module=(E/'NCC_fullframes.rs.txt').read_text();assert hashlib.sha256(module.encode()).hexdigest()==installed['module_sha256']
patch+=''.join(difflib.unified_diff([],module.splitlines(True),fromfile='/dev/null',tofile='b/'+n))
(E/'NCC_stage3_harness.patch').write_text(patch)
(E/'NCC_PATCH_PINS.json').write_text(json.dumps({p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in E.glob('NCC_*.patch')},indent=2)+'\n')
print(len(rows),'native sources pinned; cumulative patch exported')
