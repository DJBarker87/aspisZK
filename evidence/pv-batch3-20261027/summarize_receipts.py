from pathlib import Path
import json,hashlib,re,sys
D=Path(__file__).resolve().parent;t=json.loads((D/'TALLY.json').read_text());rows=[];accepted=[]
for p in sorted((D/'receipts').glob('*/receipt/receipt.json')):
 r=json.loads(p.read_text());rows.append(dict(label=p.parent.parent.name,target=r.get('command'),exit=r.get('exit_status'),wall_seconds=r.get('wall_seconds'),peak_rss_kib=r.get('peak_rss_kib'),cgroup_memory_peak_bytes=r.get('cgroup_memory_peak_bytes'),swaps=r.get('swaps'),source_revision=r.get('source_revision'),effective_binary_source_revision=r.get('effective_binary_source_revision'),source_sha256=r.get('source_sha256'),print_axioms=r.get('print_axioms'),receipt=str(p)))
 if r.get('attempt') is not None and r.get('exit_status')==0:
  log=(p.parent/'stdout.log').read_text()+(p.parent/'stderr.log').read_text()
  assert not re.search(r'\b(sorryAx|native_decide|implemented_by)\b',log),(p,'forbidden accepted audit')
  for a in re.findall(r'depends on axioms: \[([^]]*)\]',log):
   vals={x.strip()for x in a.split(',')if x.strip()};assert vals<={'propext','Classical.choice','Quot.sound'},(p,vals)
  accepted.append(r['attempt'])
(D/'receipt-index.json').write_text(json.dumps(dict(lean_budget=t['lean_budget'],charged_lean_attempts=t['lean_attempts'],kani_attempts=t['kani_attempts'],used_ids=t['used_ids'],refusals=t['refusals'],accepted_attempts=accepted,runs=rows),indent=2)+'\n')
# Current-source coverage is recorded separately from rejected historical drafts.
coverage=[]
for p in sorted((D/'lean').glob('*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest();matching=[]
 for row in rows:
  if row['source_sha256']==sha and row['exit']==0:matching.append(row['label'])
 coverage.append(dict(module=p.stem,sha256=sha,accepted_receipts=matching))
(D/'current-source-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
print(json.dumps(dict(charged=t['lean_attempts'],used_ids=len(t['used_ids']),accepted=len(accepted),current_modules=len(coverage),missing=[r['module']for r in coverage if not r['accepted_receipts']])))
