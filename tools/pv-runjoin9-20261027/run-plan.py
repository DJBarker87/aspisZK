#!/usr/bin/env python3
"""Sequential proof targets and mandated reservation waits; no host infrastructure changes."""
import datetime,json,pathlib,subprocess,sys,time
root=pathlib.Path(__file__).resolve().parents[2]; e=root/'evidence/pv-runjoin9-20261027'
plan=json.loads((root/sys.argv[1]).read_text()); plan=plan.get('missing',[]) if isinstance(plan,dict) else plan
start,count,attempt=map(int,sys.argv[2:5])
if len(sys.argv)>5:
 prior=json.loads((e/f'refusal-{sys.argv[5]}.json').read_text())
 until=datetime.datetime.fromisoformat(prior['utc']).timestamp()+180
 while time.time()<until:time.sleep(min(30,until-time.time()))
for row in plan[start:start+count]:
 for retry in range(11):
  assert attempt<=37699
  charged=sum(json.loads(p.read_text()).get('exit') is not None for p in e.glob('receipt-*.json'))
  audit=row['module'].startswith('R1Z.PV_RunJoin_TrustAudit9')
  assert charged<(100 if audit else 97),'Last three attempts reserved for focused audit'
  assert not audit or charged>=97,'Focused audits run only in the final three attempts'
  r=subprocess.run([sys.executable,str(root/'tools/pv-runjoin9-20261027/check.py'),str(attempt),row['module'].replace('.','/'),row['source']],capture_output=True,text=True)
  print('\n'.join(s for s in r.stdout.splitlines() if s.startswith(('LAUNCH','RECEIPT','RESERVATION'))),flush=True)
  used=attempt;attempt+=1
  if r.returncode==0:break
  if r.returncode!=78:
   print(r.stdout[-4500:]+r.stderr,flush=True);sys.exit(r.returncode)
  if retry==10:sys.exit(78)
  with (e/'waits.jsonl').open('a') as f:f.write(json.dumps(dict(refused_id=used,next_id=attempt,seconds=180,module=row['module']))+'\n')
  until=time.time()+180
  while time.time()<until:time.sleep(min(30,until-time.time()))
print('PLAN COMPLETE; next unused ID',attempt,flush=True)
