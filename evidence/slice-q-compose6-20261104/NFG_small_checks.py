"""Whole-body scalar/record contract packet checks; no closure by assertion."""
from pathlib import Path
import hashlib,json,lzma,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
obj=lambda p:json.loads(p.read_text())
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def check():
 out=[]
 for a,status in [('NFG_K019',0),('NFG_K020',1),('NFG_K021',0),('NFG_K022',1),('NFG_K024',0),('NFG_K025',1)]:
  r=obj(E/a/'receipt.json');assert r['exit_status']==status and r['limits']==LIMITS and int(r['swaps'])==0
  ad=obj(E/(a+'-admission.json'));assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
  log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' if status==0 else 'VERIFICATION:- FAILED') in log
  assert 'timed out' not in log.lower() and 'unwinding assertion' not in log.lower()
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert r['copy_patch_sha256']==sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())
  graph=obj(E/(a+'-graph-check.json'));assert graph['graph_matches_frozen'] and graph['exact_frozen_selected_graph']
  lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert obj(E/(a+'-source-check.json'))['errors']==[]
  raw=lzma.decompress((E/(a+'_INPUTS.json.xz')).read_bytes());assert sha(raw)==(E/(a+'_INPUTS.json.sha256')).read_text().strip()
  payload=json.loads(raw)
  # Archive format checked below; complete native source hash table binds the reference.
  for name,h in r['source_hashes'].items():assert sha(payload[name].encode())==h,(a,name,'archived input drift')
  pins=json.loads(payload['NFG_SOURCE_PINS.json'])
  assert pins['NFG_small_refs.rs']==sha((E/'NFG_small_refs.rs.txt').read_bytes())
  assert all(f['features']==['r0'] for f in graph['resolved_features_all_crates'] if f['name']=='aspis-core')
  out.append({'attempt':a,'receipt_sha256':sha((E/a/'receipt.json').read_bytes()),'exit':status})
 # The exact byte-identical reference was frozen in every native pin table and E004.
 pins=obj(E/'NFG_SOURCE_PINS.json');ref=sha((E/'NFG_small_refs.rs.txt').read_bytes())
 assert pins['NFG_small_refs.rs']==ref
 assert obj(E/'NFG_SMALL_EXTRACTION_PINS.json')['reference_sha256']==ref
 assert (E/'NFG_small_ref/src/lib.rs').read_bytes()==(E/'NFG_small_refs.rs.txt').read_bytes()
 # Verify the only changes to actual field/core are cfg(kani) attributes/module.
 r=obj(E/'NFG_K019/receipt.json')
 raw=lzma.decompress((E/'NFG_K019_INPUTS.json.xz').read_bytes());p=json.loads(raw)
 for name in ['field.rs','lib.rs']:
  original=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/'+name],cwd=R,text=True)
  actual=p['NFG_src/crates/aspis-core/src/'+name]
  actual='\n'.join(line for line in actual.split('\n') if not any(tag in line for tag in ['#[cfg_attr(kani, kani::','#![cfg_attr(kani, feature(allocator_api))]','#[cfg(kani)] extern crate self as aspis_core;']))
  actual=actual.removesuffix('\n#[cfg(kani)] pub mod NFG_contract;\n')
  assert actual==original,(name,'frozen source fission drift')
 configs=[]
 for a in ['NFG_K019','NFG_K021','NFG_K024','NFG_K025']:
  r=obj(E/a/'receipt.json');configs.append({n:h for n,h in r['source_hashes'].items() if n.startswith('NFG_src/')})
 assert all(c==configs[0] for c in configs),'KMX controls differ in native source payload'
 for pos,neg in [('NFG_K019','NFG_K020'),('NFG_K021','NFG_K022')]:
  a=obj(E/pos/'receipt.json');b=obj(E/neg/'receipt.json');assert a['target']==b['target'] and a['source_hashes']==b['source_hashes']
 return dict(native=out,reference_sha256=ref,extraction_receipt_sha256=sha((E/'NFG_E004/receipt.json').read_bytes()),status='LOCAL_SUPPORT; caller installation is separately required')
if __name__=='__main__':print(json.dumps(check(),indent=2))
