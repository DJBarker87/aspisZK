from pathlib import Path
import json,subprocess
E=Path('evidence/pv-batch2-20261027/batch2f');D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';H='dombarker@100.108.41.90'
rels=['candidate/batch2f-fixtures-001/'+x for x in ['command.json','receipt/receipt.json','receipt/stdout.log','receipt/stderr.log','receipt/time.log']]
rels+=['batch2f-fixture-gate-001/'+x for x in ['plan.json','runs.json','comparison.json']+[f'sample-{i}.{s}' for i in range(5) for s in ['log','time.log']]]
for rel in rels:
 r=subprocess.run(['ssh',H,'cat '+D+'/'+rel],capture_output=True,check=True);p=E/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(r.stdout)
c=json.loads((E/'batch2f-fixture-gate-001/comparison.json').read_text());assert c['passed'] and c['completed_pairs']==10
r=json.loads((E/'candidate/batch2f-fixtures-001/receipt/receipt.json').read_text());assert r['exit_status']==0
(E/'FIXTURE-GATE.json').write_text(json.dumps(dict(passed=True,comparison='batch2f-fixture-gate-001/comparison.json',receipt='candidate/batch2f-fixtures-001/receipt/receipt.json',plan=c['plan'],pairs=10,files=['proof.bin','public.bin'],result_fields=['status','attempts','callbacks','proof_sha256','audit'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],classification='Finite ordered byte/observable-result differential; not universal native correspondence'),indent=2)+'\n')
print('ten fixture pairs PASS; text/hash receipts retained')
