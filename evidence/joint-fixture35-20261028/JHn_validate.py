from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[json.loads(f.read_text()) for f in sorted(P.glob('JHn35_[0-9][0-9][0-9]/receipt.json'))]
allowed={'propext','Classical.choice','Quot.sound'}
issues=[];latest={};counts={}
for r in rows:
 a=r['attempt'];counts[a]=counts.get(a,0)+1
 limits=r['limits'];want={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if limits!=want:issues.append([a,'limits',limits])
 if int(r['swaps'])!=0:issues.append([a,'swap',r['swaps']])
 admission=json.loads((P/(a+'-admission.json')).read_text())[-1]
 if not (admission['exit_status']==0 and admission['receipt'].get('allowed') is True):issues.append([a,'admission',admission])
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if 'axioms: [' in line:
    names=set(line.split('axioms: [',1)[1].split(']',1)[0].split(', '))
    if not names<=allowed:issues.append([a,'nonstandard root axioms',line])
  for source,sha in r['source_hashes'].items():latest[source]=dict(attempt=a,sha256=sha)
active={}
for f in sorted((R/'lean').glob('JHn_*.lean')):
 sha=hashlib.sha256(f.read_bytes()).hexdigest();prev=latest.get(f.name)
 if not prev or prev['sha256']!=sha:issues.append([f.name,'no current successful receipt',prev])
 active[f.name]=dict(sha256=sha,bytes=f.stat().st_size,receipt=prev)
for f in (R/'lean').glob('JHn_*.lean'):
 for i,line in enumerate(f.read_text().splitlines(),1):
  if re.search(r'^\s*(axiom\s|opaque\s)|\b(sorry|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',line):issues.append([str(f.relative_to(R)),i,line])
checks=[]
for script in ['JHn_generate.py','JHn_restore_sources.py']:
 result=subprocess.run(['python3',str(P/script),'--check'],capture_output=True,text=True)
 checks.append(dict(command=script+' --check',exit=result.returncode,stdout=result.stdout,stderr=result.stderr))
 if result.returncode:issues.append([script,result.stderr])
base=json.loads((P/'JHn_PREFLIGHT.json').read_text())['initial_revision']
x=subprocess.run(['git','diff','--check',base],cwd=R,capture_output=True,text=True);checks.append(dict(command='git diff --check '+base,exit=x.returncode,stdout=x.stdout,stderr=x.stderr))
if x.returncode:issues.append(['diff check',x.stdout,x.stderr])
(P/'JHn_ACTIVE_SOURCES.json').write_text(json.dumps(active,indent=2)+'\n')
summary=dict(attempts=len(rows),settled=len(rows),success=sum(r['exit_status']==0 for r in rows),failed=sum(r['exit_status']!=0 for r in rows),active_sources=len(active),issues=issues,checks=checks)
(P/'JHn_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
raise SystemExit(bool(issues))
