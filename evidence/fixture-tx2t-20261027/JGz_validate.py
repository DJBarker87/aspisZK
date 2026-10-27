"""Compile-free current-hash, budget, admission and axiom receipt audit."""
from pathlib import Path
import hashlib,json,re,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[];passed={};problems=[]
for f in sorted(P.glob('JGz_TX2_*/receipt.json')):
 d=json.loads(f.read_text());a=d['attempt'];rows.append(d)
 for n,h in d['source_hashes'].items():
  src=R/'lean'/n
  if d['exit_status']==0 and src.exists() and hashlib.sha256(src.read_bytes()).hexdigest()==h:passed[n]=a
 if d['exit_status']==0:
  for line in d['print_axioms']:
   if 'does not depend on any axioms' in line:continue
   m=re.search(r'axioms:\s*\[([^\]]*)\]',line,re.S)
   if not m or not set(x.strip() for x in m[1].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}:problems.append([a,'nonstandard or unparsed axiom',line])
 admission=json.loads((P/(a+'-reservation.json')).read_text())
 if admission.get('allowed') is not True:problems.append([a,'not admitted'])
 limits=d.get('limits',{})
 for k,v in {'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}.items():
  if str(limits.get(k))!=v:problems.append([a,'wrong cap',k,limits.get(k)])
 if '-M7000' not in d['command']:problems.append([a,'missing -M7000'])
 if int(d['swaps']):problems.append([a,'nonzero swaps'])
new=list((R/'lean').glob('JGz_*.lean'))
for f in new:
 if f.name not in passed:problems.append([f.name,'no passing current-hash receipt'])
 s=f.read_text()
 if re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option\s+max(?:RecDepth|Heartbeats)',s,re.M):problems.append([f.name,'forbidden proof construct'])
 if f.name not in ('JGz_TopAudit.lean',):
  for m in re.finditer(r'^theorem (\w+)',s,re.M):
   if '#print axioms '+m[1] not in s:problems.append([f.name,'missing theorem axiom command',m[1]])
summary=dict(attempts=len(rows),passed=sum(d['exit_status']==0 for d in rows),rejected=sum(d['exit_status']!=0 for d in rows),Kani=0,wall_seconds=sum(d['wall_seconds'] for d in rows),peak_rss_kib=max((int(d['peak_rss_kib']) for d in rows),default=0),swaps=sum(int(d['swaps']) for d in rows),current_sources=len(new),checked_current_sources=len(passed),problems=problems)
(P/'JGz_VALIDATION.json').write_text(json.dumps(passed,indent=2)+'\n')
(P/'JGz_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'JGz_ATTEMPTS.jsonl').write_text(''.join(json.dumps(d)+'\n' for d in rows))
print(json.dumps(summary,indent=2))
if '--final' in sys.argv:
 assert len(rows)==100,'Whole-budget work incomplete'
 assert not problems,'Current validation incomplete'
