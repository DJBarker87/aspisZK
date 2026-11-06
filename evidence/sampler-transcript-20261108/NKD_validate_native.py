"""Validate same-configuration positives and semantic controls, source hashes and parity."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for a,b,target,index in [('NKD_K007','NKD_K002','deployed_new_cut',0),('NKD_K003','NKD_K004','deployed_absorb_cut',0),('NKD_K005','NKD_K006','deployed_block_cut',2)]:
 pair=[]
 for n,negative in [(a,False),(b,True)]:
  r=json.loads((E/n/'receipt.json').read_text());cfg=json.loads((E/(n+'.json')).read_text());log=(E/n/'stdout.log').read_text()
  assert r['module']=='NKD_native::'+target;assert r['exit_status']==int(negative)
  assert ('VERIFICATION:- FAILED'if negative else 'VERIFICATION:- SUCCESSFUL')in log
  assert 'Manual Harness Summary:'in log and not re.search(r'(?i)timed out|out of memory|unwinding assertion.*FAILURE',log)
  if negative:assert f'Failed Checks: assertion failed: (out.state[l.k]==l.replies[{index}][l.k])!=cfg!(NKD_invert)'in log
  assert r['limits']==expected;assert r['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-sampler-transcript-20261108/NKD_target')
  assert r['env']['CARGO_NET_OFFLINE']=='true';assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3';assert '--locked'not in cfg['native_command']
  for rel,h in r['source_hashes'].items():assert sha(E/n/'sources'/rel)==h
  pins=json.loads((E/n/'sources/NKD_SOURCE_PINS.json').read_text());assert pins['programs/r1-cost-probe/src/NKD_native.rs']==sha(E/'NKD_native_generated.rs.txt')
  assert pins['KMX_stubs.rs']=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
  assert pins['KMX_native.rs']=='cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880'
  g=json.loads((E/(n+'-graph-check.json')).read_text());assert g['graph_matches_frozen']and not g['edge_errors']and not g['new_package_tuples']
  fs={z['name']:z['features']for z in g['selected_closure']}
  assert set(['default','pool-adapter','private-leaf-salts'])<=set(fs['aspis-r1-cost-probe-program'])
  assert set(['default','optimized-terminal','private-leaf-salts','program-build'])<=set(fs['aspis-r1-cost-probe'])
  assert set(['r0','pool-v1-kernel'])<=set(fs['aspis-statement'])
  l=json.loads((E/(n+'-lock-check.json')).read_text());assert l['unchanged']and l['before']==l['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  ad=json.loads((E/(n+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True
  pair.append(r)
 assert pair[0]['source_hashes']==pair[1]['source_hashes']
 rows.append(dict(positive=a,negative=b,target=target,positive_receipt_sha256=sha(E/a/'receipt.json'),negative_receipt_sha256=sha(E/b/'receipt.json'),source_hashes=pair[0]['source_hashes'],deployed_features=fs,semantic_negative=True))
s=(E/'NKD_native_generated.rs.txt').read_text();assert not re.search(r'\bstatic\s+(?:mut\s+)?\w+\s*:',s)and 'Option<fn'not in s and 'stub_verified'not in s
(E/'NKD_NATIVE_MATRIX.json').write_text(json.dumps(dict(status='PASS',pairs=rows,copy_patch_sha256=sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',compiled_source_sha256=sha(E/'NKD_native_generated.rs.txt'),quarantined=[],suspended=[],excluded=['NKD_K001 compile error; no solver credit']),indent=1)+'\n')
print('PASS: three deployed native/control pairs; zero quarantine or suspension')
