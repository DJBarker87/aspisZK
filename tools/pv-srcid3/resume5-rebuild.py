#!/usr/bin/env python3
"""Sequential charged missing-object rebuild; no automatic unchanged retry."""
import json,pathlib,subprocess,sys,time,datetime
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
p=json.loads((e/'resume5-plan.json').read_text()); rows={r['module']:r for r in p['rows']}
start=int(sys.argv[1]);mode=sys.argv[2]; limit=int(sys.argv[3])
refusals=0
queue=list(p['order'])
while queue:
 m=queue.pop(0)
 ledger=e/'resume5-attempts.jsonl'; prior=[json.loads(s) for s in ledger.read_text().splitlines()] if ledger.exists() else []
 if len(prior)>=100:break
 if any(x['module']==m.replace('.','/') for x in prior):continue
 if mode=='research' and not rows[m]['research_source_exists']:continue
 if limit<=0:break
 # Refusals consume IDs, but never count as Lean attempts. Caller waits and resumes.
 print('START',start,m,flush=True)
 r=subprocess.run([sys.executable,str(root/'tools/pv-srcid3/resume5-compile.py'),str(start),m.split('.')[-1]],capture_output=True,text=True)
 (e/f'client-{start}.log').write_text(r.stdout+r.stderr)
 print('END',start,r.returncode,(r.stdout+r.stderr)[-1600:],flush=True)
 (e/'resume5-next-id.txt').write_text(str(start+1)+'\n')
 if r.returncode==78:
  refusals+=1
  if refusals>=10:sys.exit(78)
  start+=1;queue.insert(0,m)
  for _ in range(3):
   print('reservation wait: 60 seconds',flush=True);time.sleep(60)
  continue
 refusals=0
 if r.returncode and not any(json.loads(x)['attempt']==start for x in ledger.read_text().splitlines()) if ledger.exists() else bool(r.returncode):sys.exit(r.returncode)
 start+=1;limit-=1
