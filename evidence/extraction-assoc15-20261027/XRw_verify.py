"""Read-only validation and aggregation of proof receipts (no prover launch)."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
rs=sorted((json.loads(p.read_text()) for p in E.glob('XRw_L*/receipt.json')),key=lambda r:r['attempt'])
errors=[]
for r in rs:
 a=r['attempt']; log=(E/a/'stdout.log').read_text()
 for k,v in r['source_hashes'].items():
  p=E/a/'sources'/k
  if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest()!=v:errors.append([a,'source hash',k])
 lim=r['limits']
 for k,v in [('memory.high','6442450944'),('memory.max','8589934592'),('memory.swap.max','0'),('pids.max','64')]:
  if str(lim[k])!=v:errors.append([a,'limit',k,lim[k]])
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append([a,'admission'])
 if r['exit_status']==0:
  for line in r['print_axioms']:
   groups=re.findall(r'\[([^]]*)\]',line)
   names=[x.strip() for x in groups[-1].split(',') if x.strip()] if groups else []
   if any(x not in {'propext','Classical.choice','Quot.sound'} for x in names):errors.append([a,'axioms',line])
 if '-M7000' not in r['command'] or '-j1' not in r['command']:errors.append([a,'command caps'])
(E/'XRw_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rs))
v=dict(attempts=len(rs),passed=sum(r['exit_status']==0 for r in rs),failed=sum(r['exit_status']!=0 for r in rs),kani_runs=0,
 wall_seconds=sum(r['wall_seconds'] for r in rs),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=sum(int(r['swaps']) for r in rs),validation_errors=errors)
(E/'XRw_VERIFICATION.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
