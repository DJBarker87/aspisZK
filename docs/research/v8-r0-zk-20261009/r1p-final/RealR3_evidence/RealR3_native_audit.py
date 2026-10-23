"""Audit existing native receipts/snapshots, preserving all failed diagnostics."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 name=p.parent.name;r=json.loads(p.read_text());i=json.loads((E/(name+'-inputs.json')).read_text());log=(p.parent/'stdout.log').read_text()
 for f,h in i['hashes'].items():
  s=E/'snapshots'/name/(f+'.txt');assert hashlib.sha256(s.read_bytes()).hexdigest()==h,(name,f)
 limits=r['limits'];assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},limits
 assert r['env']['RUSTFLAGS'].startswith('-C opt-level=3 ')
 passed=r['exit_status']==0
 if passed:assert 'VERIFICATION:- SUCCESSFUL' in log and '0 failures, 1 total' in log
 rows.append({'name':name,'source_revision':i['source_revision'],'input_hashes':i['hashes'],'reservations':i['reservations'],**r,'verified':passed,'diagnostic':'accepted bounded congruence/serialization check' if passed else 'compile error or no verdict; inspect stdout/stderr','native_axioms':'N/A: external P6 gate; not a Lean axiom'})
(E/'RealR3_native-attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps([{k:r[k] for k in ['name','exit_status','wall_seconds','peak_rss_kib','swaps','verified']} for r in rows],indent=2))
