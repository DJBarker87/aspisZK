"""Audit task receipts, exact final sources, standard axioms and unchanged top."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[]
for f in sorted(P.glob('JFq_[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(f.read_text());r['receipt']=str(f.relative_to(R))
 r['errors']=[s for s in f.with_name('stdout.log').read_text().splitlines() if 'error:' in s or 'error(' in s]
 rows.append(r)
(P/'JFq_RECORDS_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
valid={};missing=[]
for f in sorted((R/'lean').glob('JFq_*.lean')):
 sha=hashlib.sha256(f.read_bytes()).hexdigest()
 matches=[r for r in rows if r['exit_status']==0 and r['source_hashes'].get(f.name)==sha]
 if not matches:missing.append(f.name);continue
 r=matches[-1]
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  if 'depends on axioms:' in line:
   ax=line.split('depends on axioms:',1)[1].strip().strip('[]')
   assert set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},line
 valid[f.name]=dict(sha256=sha,attempt=r['attempt'],receipt=r['receipt'],axioms=r['print_axioms'])
(P/'JFq_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
source=(R/'lean/Rc8_Top.lean').read_bytes();(P/'JFq_AFTER_Rc8_Top.lean.txt').write_bytes(source)
ledger=json.loads((P/'JFq_LEDGER_DELTA.json').read_text());before=(P/'JFq_BEFORE_Rc8_Top.lean.txt').read_bytes()
ledger.update(source_statements_identical=before==source,before_source_sha256=hashlib.sha256(before).hexdigest(),after_source_sha256=hashlib.sha256(source).hexdigest())
assert before==source
(P/'JFq_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
preflight_stops=list(P.glob("JFq_[0-9][0-9][0-9]_PREFLIGHT_STOP.json"))
summary=dict(charged=len(rows)+len(preflight_stops),lean_processes=len(rows),passes=sum(r['exit_status']==0 for r in rows),rejects=sum(r['exit_status']!=0 for r in rows),kani=0,checked_modules=len(valid),unaccepted_current_sources=missing,wall_seconds=sum(r['wall_seconds'] for r in rows),max_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows))
(P/'JFq_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(summary)
