"""Summarize retained receipts, keeping failures and P6 evidence distinct."""
from pathlib import Path
import json,re
E=Path(__file__).resolve().parents[2]/'evidence/pv-runjoin12-20261027'
rows=sorted((json.loads(p.read_text()) for p in E.glob('receipt-*.json')),key=lambda r:r['attempt'])
actual=[r for r in rows if r.get('exit') is not None];passed=[r for r in actual if r.get('accepted')]
allowed={'propext','Classical.choice','Quot.sound'}
for r in passed:
 for ax in r.get('axioms',[]):
  if 'depends on axioms:' not in ax:continue
  found=re.search(r'\[([\s\S]*?)\]',ax)
  if found:
   names=set(re.findall(r'[A-Za-z_][\w.]*',found[1]));assert names<=allowed,(r['attempt'],names)
summary=dict(lean_charged=len(actual),accepted=len(passed),rejected=len(actual)-len(passed),used_ids=sorted(int(p.stem.split('-')[1]) for p in E.glob('used-*.json')),max_accepted_rss_bytes=max((r.get('peak_rss_bytes',0) for r in passed),default=0),accepted_swap_total=sum(r.get('swaps',0) for r in passed),accepted_axioms=sorted(allowed),axioms_audit='all retained accepted #print axioms outputs checked; missing output not invented',kani_charged=len((E/'kani-invocations.jsonl').read_text().splitlines()),R_shipped='OPEN',target='not established')
(E/'receipt-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
columns=['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','accepted']
(E/'lean-receipts.tsv').write_text('\t'.join(columns)+'\n'+'\n'.join('\t'.join(str(r.get(c,'')) for c in columns) for r in actual)+'\n')
print(summary)
