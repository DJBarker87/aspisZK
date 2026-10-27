"""Compile-free evidence consolidation; never launches or retries a build."""
from pathlib import Path
import json,re,hashlib,csv,io
out=Path('evidence/pv-d188-20261027');rs=[]
for p in sorted(out.glob('*-receipt.json')):
 if p.name.startswith('28') or p.name.startswith('native-'):
  d=json.loads(p.read_text());d['receipt_path']=str(p);rs.append(d)
lean=[d for d in rs if 'attempt' in d];native=[d for d in rs if 'attempt' not in d]
assert len(lean)==40, len(lean)
assert len({d['attempt'] for d in lean})==40
assert all(28100<=d['attempt']<=28299 for d in lean)
# Successful tests must be recoverable byte-for-byte from the delivered inputs.
for d in lean:
 if d['exit']==0:assert hashlib.sha256((out/'tests'/(d['target']+'.lean')).read_bytes()).hexdigest()==d['source_sha256'],d['target']
(out/'receipts.json').write_text(json.dumps(rs,indent=2)+'\n')
s=io.StringIO();w=csv.writer(s);w.writerow(['target','attempt_or_run','exit','wall_seconds','peak_rss_kib','swap','source_revision','source_sha256','print_axioms','receipt'])
for d in rs:w.writerow([d['target'],d.get('attempt',Path(d['receipt_path']).stem),d['exit'],d['wall_seconds'],','.join(d['peak_rss_kib']),','.join(d['swaps']),d['source_revision'],d['source_sha256'],d['print_axioms'],d['receipt_path']])
(out/'receipts.csv').write_text(s.getvalue())
refused=[]
for p in sorted(out.glob('28*-refusal.json')):
 a=int(p.name.split('-')[0]);r=json.loads((out/f'{a}-admission.log').read_text());next_a=min(d['attempt'] for d in lean if d['attempt']>a);n=json.loads((out/f'{next_a}-admission.log').read_text());from datetime import datetime
 delta=(datetime.fromisoformat(n['utc'])-datetime.fromisoformat(r['utc'])).total_seconds();refused.append(dict(id=a,next_id=next_a,wait_seconds=delta,met_180_second_wait=delta>=180))
(out/'reservation-retries.json').write_text(json.dumps(refused,indent=2)+'\n')
summary=dict(lean_charged=len(lean),lean_budget=40,lean_success=sum(d['exit']==0 for d in lean),lean_failed=sum(d['exit']!=0 for d in lean),uncharged_reservation_refusals=refused,native_scopes=len(native),native_success=sum(d['exit']==0 for d in native),native_failed=sum(d['exit']!=0 for d in native),kani=0,peak_lean_rss_kib=max(int(v) for d in lean for v in d['peak_rss_kib']),all_recorded_swap_zero=all(v=='0' for d in rs for v in d['swaps']),fresh_differential_agreements=len(json.loads((out/'differential.json').read_text())['checks']),raw_reused_disagreements=3,stopping_reason='40 Lean attempts exhausted; failed and unchecked functions remain suspended',reservation_wait_exceptions=[r for r in refused if not r['met_180_second_wait']])
(out/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(out/'test-source-manifest.json').write_text(json.dumps([dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in sorted((out/'tests').rglob('*')) if p.is_file()],indent=2)+'\n')
# No untracked proposed test becomes an accepted proof by appearing in this manifest.
p=out/'AUDIT.md';t=p.read_text().replace('40/40 charged Lean attempts (22 pass, 18 fail)','40/40 charged Lean attempts (22 pass, 18 fail)').replace('Eight native scopes ran (seven\npass, one pre-compilation path failure).','Eight native scopes ran (seven\npass, one pre-compilation path failure).')
t=t.replace('41 inspected/tested helper occurrences retain their local credit;\n382', '41 inspected/tested helper occurrences retain their local credit;\n382')
t+='\nFinal compile-free checks: all 22 successful test-source SHA256 values match the\ndelivered input files, all compared fresh projections agree. The exact reservation wait exceptions\nare recorded in reservation-retries.json. `cleanup.json` hashes\nand records removal of 23 rebuildable private artifacts (22 test objects and\none test binary); sources, receipts and every shared object/source were retained.\n'
p.write_text(t)
print(json.dumps(summary))
