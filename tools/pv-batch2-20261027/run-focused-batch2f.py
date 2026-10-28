"""Sequential focused proof queue; every refusal consumes a fresh ID after cooldown."""
from pathlib import Path
import json,subprocess,sys,time,datetime,hashlib
E=Path('evidence/pv-batch2-20261027/batch2f');L=Path('docs/research/v8-r0-zk-20261009/lean')
queue=sys.argv[1:]
for m in queue:
 sha=hashlib.sha256((L/(m+'.lean')).read_bytes()).hexdigest()
 t=json.loads((E/'TALLY.json').read_text())
 if any(a['module']==m and a.get('exit')==0 and json.loads((E/(str(a['id'])+'.json')).read_text())['source_sha256']==sha for a in t['attempts']):continue
 for retry in range(10):
  until=0
  for hold in list(E.glob('*-reservation.log'))+list(E.glob('*-admission-barrier.json')):
   try:
    r=json.loads(hold.read_text())
    if r.get('allowed') is False:until=max(until,datetime.datetime.fromisoformat(r['utc']).timestamp()+180)
   except (ValueError,KeyError):pass
  while time.time()<until:time.sleep(min(55,until-time.time()+0.1))
  t=json.loads((E/'TALLY.json').read_text());assert t['lean_charged']<57
  used={a['id'] for a in t['attempts']}|set(json.loads((E/'ID-PREFLIGHT.json').read_text())['used'])
  n=next(n for n in range(40800,40897) if n not in used)
  print('focused dependency',n,m,'admission try',retry+1,flush=True)
  r=subprocess.run([sys.executable,'tools/pv-batch2-20261027/lean-batch2f.py',str(n),m])
  if r.returncode==0:break
  if (E/(str(n)+'.json')).exists():raise SystemExit(r.returncode)
  if (E/'HOST-BARRIER-STOP.json').exists():raise SystemExit('recorded barrier error; inspect p_prime classification')
  if r.returncode!=78:raise SystemExit(r.returncode)
 else:raise SystemExit('ten ordinary admission refusals; no compiler launched; compile-free review required')
