"""Summarize retained receipts; failed elaborations never receive proof credit."""
from pathlib import Path
import json
D=Path('evidence/pv-b3p6-20261028');rows=[]
for p in sorted((D/'receipts').glob('*/receipt/receipt.json')):
 r=json.loads(p.read_text());kind='Lean' if 'module' in r else ('Kani' if 'kani' in r['command'] else 'tool/native')
 stdout=(p.parent/'stdout.log').read_text();stderr=(p.parent/'stderr.log').read_text()
 if kind=='Lean' and r['exit_status']==0:
  assert 'sorryAx' not in stdout+stderr,p
  for line in stdout.splitlines():
   if 'depends on axioms:' in line:
    names=line.split('depends on axioms:',1)[1].strip().strip('[]').split(', ')
    assert set(names)<={'propext','Classical.choice','Quot.sound'},(p,names)
 rows.append({'target':p.parts[-3],'kind':kind,'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swap':r['swaps'],'cgroup_peak_bytes':r.get('cgroup_memory_peak_bytes'),'source_revision':r['source_revision'],'proof_revision':r.get('lean_source_revision'),'module':r.get('module'),'axioms':r.get('print_axioms','not recorded'),'proof_credit':kind=='Lean' and r['exit_status']==0,'receipt':str(p),'RSS_caveat':'timeout-parent RSS may omit descendants; use cgroup peak too' if r['exit_status']==124 else None})
(D/'receipt-index.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'retained_receipts':len(rows),'successful_Lean_modules':sum(r['proof_credit'] for r in rows),'Kani_commands':sum(r['kind']=='Kani' for r in rows),'note':'partial retained snapshot; authoritative current counter is host TALLY'}))
