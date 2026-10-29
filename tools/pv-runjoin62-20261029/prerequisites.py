from pathlib import Path
import json,subprocess,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin62-20261029';T=Path(__file__).parent
mods=json.loads((E/'native-dependency-remaining.json').read_text());a=70600
for m in mods:
 if a>70696:raise SystemExit('Budget reserve reached')
 while True:
  r=subprocess.run([sys.executable,str(T/'focused.py'),str(a),m])
  if r.returncode in [77,78]:
   for _ in range(6): print('admission cooldown',m,flush=True);time.sleep(30)
   continue
  if r.returncode:raise SystemExit(r.returncode)
  break
 a+=1
print('PREREQUISITES COMPLETE next ID',a,flush=True)
