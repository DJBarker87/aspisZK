"""Read-only focused proof receipt audit, independent of pending source status."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028';allowed={'propext','Classical.choice','Quot.sound'};rows=[];seen=set()
for p in sorted(E.glob('receipt-[0-9]*.json')):
 r=json.loads(p.read_text());snap=E/r['source_snapshot'];assert hashlib.sha256(snap.read_bytes()).hexdigest()==r['source_sha256']
 raw=subprocess.check_output(['git','show',r.get('source_capture_revision',r['source_revision'])+':'+r['source_path']]);assert hashlib.sha256(raw).hexdigest()==r['source_sha256']
 assert subprocess.check_output(['git','rev-parse',r.get('source_capture_revision',r['source_revision'])+':'+r['source_path']],text=True).strip()==r.get('source_capture_git_blob',r['source_git_blob'])
 assert all(x in r['command'] for x in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64','7000'])
 assert r['reservation']['allowed'] is True
 key=(r['source_sha256'],r['deps_fingerprint']);assert key not in seen;seen.add(key)
 if r['accepted']:
  assert r['exit']==0 and r['swaps']==0
  assert r['axioms'] or not re.search(r'^\s*(?:theorem|lemma)\s',snap.read_text(),re.M)
  for a in r['axioms']:
   assert 'sorryAx' not in a
   if 'depends on axioms:' in a:assert set(re.search(r'axioms: \[([^]]*)\]',a,re.S)[1].replace('\n','').replace(' ','').split(','))<=allowed
 rows.append(r)
assert not subprocess.check_output(['git','diff','1e5edf7d8d','--','crates','programs'])
latest={r['source_path']:r for r in rows if r['accepted']};status=[]
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*31.lean')):
 rel=str(p.relative_to(R));r=latest.get(rel);status.append(dict(path=rel,accepted_current_source=bool(r and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']),accepted_attempt=r['attempt'] if r else None))
(E/'receipt-integrity.json').write_text(json.dumps(dict(receipts=len(rows),charged=sum(r['exit'] is not None for r in rows),all_source_snapshots_and_git_blobs_match=True,accepted_axioms_standard=True,all_caps_match=True,no_shipped_change=True,source_status=status,release_replay=False),indent=2)+'\n')
print('Validated',len(rows),'receipts; pending current sources:',[Path(s['path']).name for s in status if not s['accepted_current_source']])
