"""Summarize retained receipts without running Lean or treating an empty audit as clean."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('RPy_*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];cfg=json.loads((E/(a+'.json')).read_text())
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command']
 assert r['source_hashes'] and r['source_revision']=='7d1ea416bd4c185e63c278623727adc4f3c9c483'
 assert cfg['deps_fingerprint']==r['deps_fingerprint']
 rows.append(dict(attempt=a,target=r['sources'][0],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swaps=int(r['swaps']),source_revision=r['source_revision'],source_sha256=next(iter(r['source_hashes'].values())),deps_fingerprint_sha256=hashlib.sha256(json.dumps(r['deps_fingerprint'],sort_keys=True).encode()).hexdigest(),print_axioms=r['print_axioms'],axiom_audit_status='not run; continuation required',receipt=str(p.relative_to(E))))
summary=dict(attempts_used=len(rows),attempt_budget=400,kani_runs=0,passed=sum(r['exit_status']==0 for r in rows),failed=sum(r['exit_status']!=0 for r in rows),total_compile_wall_seconds=sum(r['wall_seconds'] for r in rows),max_peak_rss_kib=max((r['peak_rss_kib'] for r in rows),default=0),total_swaps=sum(r['swaps'] for r in rows),last_attempt=rows[-1] if rows else None,headline_replay_complete=False,axiom_audit_complete=False,premises_removed=0,ledger_delta=0,rows=rows)
(E/'RPy_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['rows','last_attempt']},indent=2))
