"""Read-only revalidation of immutable native/control receipts, not a replay."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
repo=E.parent.parent
roots=[repo/'evidence/transcript-queries-20261105',repo/'evidence/transcript-queries2-20261105',repo/'evidence/transcript-queries3-20261106']
p=E/'NJT_QREUSE.json';x=json.loads(p.read_text())
m=json.loads((roots[2]/'NHK_MEMBERSHIP_CALLEES.json').read_text())
pairs=[tuple(z) for z in x['selected_pairs']]
for c in m['cases']:
 pair=(c['positive'],c['control'])
 if pair not in pairs:pairs.append(pair)
if ('NGQ_K058','NGQ_K059') not in pairs:pairs.append(('NGQ_K058','NGQ_K059'))
checks=[]
for pos,neg in pairs:
 d=next(root for root in roots if (root/pos/'receipt.json').exists())
 for a,want in [(pos,0),(neg,1)]:
  r=json.loads((d/a/'receipt.json').read_text());assert r['exit_status']==want,(a,r['exit_status'])
  log=(d/a/'stdout.log').read_text();assert 'timed out' not in log.lower() and 'TimedOut' not in log,(a,'timeout')
  g=d/(a+'-graph-check.json');lock=d/(a+'-lock-check.json');assert g.exists() and lock.exists(),a
  assert json.loads(g.read_text())['graph_matches_frozen'] is True,a
  assert json.loads(lock.read_text())['unchanged'] is True,a
  assert 'VERIFICATION' in log,a
  checks.append(dict(attempt=a,receipt=str((d/a/'receipt.json').relative_to(repo)),receipt_sha256=hashlib.sha256((d/a/'receipt.json').read_bytes()).hexdigest(),graph_sha256=hashlib.sha256(g.read_bytes()).hexdigest(),lock_sha256=hashlib.sha256(lock.read_bytes()).hexdigest(),expected_exit=want))
x['selected_pairs']=pairs;x['all_revalidated_pairs']=checks;x['member_domains']=m['cases'];p.write_text(json.dumps(x,indent=2))
print('retained exact positive/control graphs and frozen locks revalidated')
