"""Audit this run's charged invocations and exact accepted sources."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin18-20261027'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-[0-9]*.json'))]
charged=[r for r in rows if r.get('exit') is not None]
assert len(charged)<=100
assert len({r['attempt'] for r in rows})==len(rows)
accepted=[r for r in rows if r['accepted']]
for r in rows:
 assert 50900<=r['attempt']<=51999
 if r['accepted']:
  assert r['exit']==0 and r['swaps']==0
  for line in r['axioms']:
   m=re.search(r'depends on axioms: \[([\s\S]*)\]',line)
   if m:assert set(x.strip() for x in m[1].split(',')) <= {'propext','Classical.choice','Quot.sound'},line
 assert hashlib.sha256((E/r['source_snapshot']).read_bytes()).hexdigest()==r['source_sha256']
seen=set()
for r in charged:
 key=(r['target'],r['source_sha256'],r['deps_fingerprint'])
 assert key not in seen,('unchanged compile',r['attempt']);seen.add(key)
(E/'receipt-index.tsv').write_text('attempt\ttarget\texit\twall_seconds\tpeak_rss_bytes\tswaps\tsource_revision\taxioms\n'+''.join('\t'.join(str(r.get(k,'')) for k in ['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','axioms'])+'\n' for r in rows))
out=dict(budget=100,charged=len(charged),accepted=len(accepted),rejected=len(charged)-len(accepted),remaining=100-len(charged),refusals=[p.name for p in sorted(E.glob('refusal-*.json'))],attempts=[r['attempt'] for r in charged],peak_rss_bytes=max((r['peak_rss_bytes'] or 0 for r in rows),default=0),swaps=sum(r['swaps'] or 0 for r in rows),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_weakened=0)
(E/'tally.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['charged','accepted','rejected','remaining','swaps']}))
