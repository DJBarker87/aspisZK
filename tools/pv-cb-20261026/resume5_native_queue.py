"""Serial remaining gates. Every refusal is collected and waited180s; no bypass.
Pauses on any non-timeout verification failure for manual counterexample review.
"""
from pathlib import Path
import subprocess,time,json,sys
p=Path(__file__).resolve().parent;ev=p.parents[1]/'evidence/pv-cb-20261026'
queue=[('compress16-lane3','compress16_lane3',180,'default'),
 ('horner-index0-lane0','horner_index0_lane0',180,'default'),
 ('horner-index0-lane1','horner_index0_lane1',180,'default'),
 ('horner-index25-lane2','horner_index25_lane2',180,'default'),
 ('horner-index25-lane3','horner_index25_lane3',180,'default'),
 ('circle','circle_sample_reference',900,'kissat'),('pole1024','pole1024_reference',900,'kissat')]
for label,harness,timeout,solver in queue:
 for retry in range(1,11):
  name=f'kani-resume5-{label}-{timeout}-q{retry:02}'
  assert not (ev/name).exists(),name
  log=ev/(name+'-driver.log')
  with log.open('w') as f:
   child=subprocess.Popen([sys.executable,str(p/'resume5_kani.py'),name,harness,str(timeout),solver],stdout=f,stderr=subprocess.STDOUT)
   sample=False
   while child.poll() is None:
    time.sleep(20)
    # Repeated read-only snapshots keep observed cgroup peak; never mutate scope.
    if (ev/name/'target.json').exists():
     r=subprocess.run([sys.executable,str(p/'resume5_scope.py'),name,'sample'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
     if r.returncode==0:sample=True
    print(name,'running' if (ev/name/'target.json').exists() else 'admission',flush=True)
  target=ev/name/'target.json'
  if not target.exists():
   # Driver-level refusal can precede native directory creation; stop to inspect.
   if not (ev/name).exists():print(log.read_text());raise SystemExit('wait guard; inspect')
   subprocess.run([sys.executable,str(p/'collect_native.py'),name],check=True)
   print(name,'UNCHARGED reservation refusal; waiting180s',flush=True)
   for i in range(6):time.sleep(30);print(name,'wait',30*(i+1),flush=True)
   continue
  subprocess.run([sys.executable,str(p/'resume5_scope.py'),name,'cleanup'],check=True)
  r=json.loads((ev/name/'collected-receipt.json').read_text())
  print(name,'COMPLETE',r['exit'],r['wall'],flush=True)
  if int(r['exit']) not in [0,124]:raise SystemExit('Review failure/counterexample before proceeding')
  break
 else:raise SystemExit('Ten refusals: return to compile-free work and retry later')
