"""Collect exact-source proof receipts and unchanged deployed-premise recounts."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for f in sorted(P.glob('JFy13_*/receipt.json')):
 r=json.loads(f.read_text());r['receipt']=str(f.relative_to(R));r['errors']=[s for s in f.with_name('stdout.log').read_text().splitlines() if 'error:' in s or 'error(' in s];rows.append(r)
assert len(rows)==100,len(rows)
(P/'JFy_RECORDS_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
valid={};unchecked={}
for f in sorted((R/'lean').glob('JFy_*.lean')):
 h=sha(f.read_bytes());matches=[r for r in rows if r['exit_status']==0 and r.get('source_hashes',{}).get(f.name)==h]
 if not matches:unchecked[f.name]=h;continue
 r=matches[-1]
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   ax=line.split('depends on axioms:',1)[1].strip().strip('[]')
   assert {x.strip() for x in ax.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},line
 valid[f.name]=dict(sha256=h,attempt=r['attempt'],receipt=r['receipt'],axioms=r['print_axioms'])
(P/'JFy_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
(P/'JFy_UNCHECKED_MANIFEST.json').write_text(json.dumps(unchecked,indent=2)+'\n')
zero=dict(T=0,P=0,G=0,C=0)
ledgers=[]
for mod,counts,actual,deployment in [('Rc7_Top',dict(T=89,P=31,G=13,C=0),dict(T=83,P=26,G=13,C=0),dict(T=6,P=5,G=0,C=0)),('Rc10_Top',dict(T=89,P=16,G=13,C=0),dict(T=83,P=12,G=13,C=0),dict(T=6,P=4,G=0,C=0))]:
 before=(P/f'JFy_BEFORE_{mod}.lean.txt').read_bytes();after=(R/'lean'/f'{mod}.lean').read_bytes();assert before==after
 (P/f'JFy_AFTER_{mod}.lean.txt').write_bytes(after)
 ledgers.append(dict(target=f'AspisR1.{mod}.deployed',method='PREMISE-LEDGER Recount on Rc7: quantified atomic-law families; conjunction leaves, guards, installed dictionaries and same witnesses retained; deployment included; alias deduplicated',before=counts,after=counts,actual=actual,deployment_non_alias=deployment,removed=zero,added=zero,changed=zero,before_source_sha256=sha(before),after_source_sha256=sha(after),source_statements_identical=True))
(P/'JFy_LEDGER_DELTA.json').write_text(json.dumps(ledgers,indent=2)+'\n')
summary=dict(charged=100,lean_processes=100,kani=0,passes=sum(r['exit_status']==0 for r in rows),rejects=sum(r['exit_status']!=0 for r in rows),wall_seconds=sum(r['wall_seconds'] for r in rows),max_reported_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),validated_modules=len(valid),unchecked=unchecked,final_attempt=rows[-1]['attempt'],final_exit=rows[-1]['exit_status'],measurement_note='GNU-time peak RSS is reported as observed; cgroup memory peak is separately retained. Focused cached composition, not fresh release replay.')
(P/'JFy_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'JFy_FAILURES.json').write_text(json.dumps([r for r in rows if r['exit_status']!=0],indent=2)+'\n')
print(summary)
