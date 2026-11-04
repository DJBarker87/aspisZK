"""Immutable same-run native windows, exact lock/features and KMX matching."""
from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def load(a):
 raw=lzma.decompress((E/(a+'_INPUTS.json.xz')).read_bytes());assert sha(raw)==(E/(a+'_INPUTS.json.sha256')).read_text().strip()
 return json.loads(raw)
def one(a,status,receipt=None):
 r=json.loads((E/a/'receipt.json').read_text()) if receipt is None else receipt
 assert r['exit_status']==status and r['limits']==LIMITS and int(r['swaps'])==0
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
 log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' if status==0 else 'VERIFICATION:- FAILED') in log
 assert 'timed out' not in log.lower() and 'unwinding assertion' not in log.lower()
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 c=r['native_command'];assert '--locked' not in c and c[c.index('--harness-timeout')+1]=='90s'
 assert r['copy_patch_sha256']==sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())
 g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph']
 fs={p['name']:p['features'] for p in g['resolved_features_all_crates']};assert fs['aspis-core']==['r0']
 if r['target'].startswith('verifier::'):
  assert c[c.index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build'
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(fs['aspis-r1-cost-probe'])
 else:assert c[c.index('--features')+1]=='r0'
 lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert json.loads((E/(a+'-source-check.json')).read_text())['errors']==[]
 data=load(a)
 for n,h in r['source_hashes'].items():assert sha(data[n].encode())==h,(a,n,'input drift')
 if 'NFG_src/crates/aspis-core/src/field/NFG_chain.rs' in data:
  s=data['NFG_src/crates/aspis-core/src/field/NFG_chain.rs'];assert 'static' not in s and 'unsafe' not in s and re.search(r'\bfn\s*\(',s) is None
 return r

def config(r):return {n:h for n,h in r['source_hashes'].items() if n.startswith('NFG_src/')}
def check():
 pairs=[(19,20,'all-raw-zero'),(21,22,'canonical-neg'),(26,27,'private-range'),(31,32,'fixed-CM-inv-G'),(33,34,'QM-square-G'),(35,36,'QM-try-inv-zero-G'),(37,38,'QM-try-inv-nonzero-G'),(41,42,'QM-neg-four-word-native-window')]
 out=[]
 for p,n,role in pairs:
  a,b=f'NFG_K{p:03}',f'NFG_K{n:03}';ra,rb=one(a,0),one(b,1)
  assert ra['target']==rb['target'] and ra['source_hashes']==rb['source_hashes']
  assert ra['env']['RUSTFLAGS'] in rb['env']['RUSTFLAGS'] and ' --cfg NFG_bad_' in rb['env']['RUSTFLAGS']
  cp,cn=(24,25) if p<26 else ((28,29) if p==26 else ((43,44) if p==41 else (39,40)))
  rc,rd=one(f'NFG_K{cp:03}',0),one(f'NFG_K{cn:03}',1)
  assert config(ra)==config(rc)==config(rd),'KMX source payload mismatch'
  out.append(dict(role=role,positive=a,negative=b,kmx_positive=f'NFG_K{cp:03}',kmx_negative=f'NFG_K{cn:03}',source_payload_sha256=sha(json.dumps(config(ra),sort_keys=True).encode()),positive_receipt_sha256=sha((E/a/'receipt.json').read_bytes()),negative_receipt_sha256=sha((E/b/'receipt.json').read_bytes()),root_credit='eligible scalar root' if p<26 else ('Range scalar support' if p==26 else ('OPEN selected cohort endpoint' if p==41 else 'OPEN abstracted callees; G/order only'))))
 return out
if __name__=='__main__':print(json.dumps(check(),indent=2))
