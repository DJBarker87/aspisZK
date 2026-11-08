"""Read-only retained source/evidence validation; never replays Lean/raw."""
from pathlib import Path
import hashlib,json,lzma,subprocess
L=Path(__file__).resolve().parent
repo=L.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
status=json.loads((L/'SESSION5_STATUS.json').read_text())
for f,h in status['sources'].items():assert sha(repo/f)==h,f
accepted=[]
for f in L.glob('receipt-497*.json'):
 r=json.loads(f.read_text());a=r['attempt'];m=r.get('target','')
 if 49737<=a<=49781 and r.get('accepted') and m.startswith('PV_LIB_SPEC_'):
  assert sha(repo/'lean'/(m+'.lean'))==r['source_sha256'],(a,m)
  assert r['exit']==0 and str(r['swaps'])=='0'
  assert all('sorryAx' not in s for s in r['axioms_summary_based'])
  accepted.append(a)
assert len(accepted)==34,len(accepted)
roots=json.loads((L/'SESSION5_RAW_ROOTS.json').read_text())
audit=json.loads((L/'SESSION5_RAW_AUDIT.json').read_text())
manifest=json.loads((L/'SESSION5_RAW_GRAPH_MANIFEST.json').read_text())
assert audit['exit']==0 and audit['all_equal'] and audit['unresolved']==0 and audit['standard_axioms_only']
assert audit['roots']==sum(v['count'] for v in roots.values())==411
for c,p in roots.items():assert {r['root'] for r in manifest['roots'] if r['cohort']==c}==set(p['roots'])
data=lzma.decompress((L/'SESSION5_RAW_GRAPH_ARCHIVE.json.xz').read_bytes())
assert hashlib.sha256(data).hexdigest()==(L/'SESSION5_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
graphs=json.loads(data)
for f in manifest['files']:assert hashlib.sha256(graphs[f['name']].encode()).hexdigest()==f['sha256']
changed=subprocess.check_output(['git','diff','--name-only',status['base']],cwd=repo,text=True).splitlines()
assert all((f.startswith('lean/PV_LIB_SPEC_') and f.endswith('.lean')) or f.startswith('evidence/pv-lib-20261107/lane-SPEC/') for f in changed)
idx=json.loads((L/'CONTRACT_INDEX.json').read_text())
assert sum(bool(r.get('whole_operational_statement_compiled')) for r in idx['rows'])==18
assert idx['full_frozen_contracts']==0 and not status['joint_witness_inhabited']
print(json.dumps({'accepted_source_receipts':len(accepted),'raw_roots':audit['roots'],'source_hashes':len(status['sources']),'lane_boundary':'PASS','full_frozen_adequacy_claimed':False,'joint_witness_inhabited':False}))
