"""One target/attempt at a time; refusal retries retain ID after full cooldown."""
from pathlib import Path
import subprocess,json,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028'
order=json.loads((E/(sys.argv[3] if len(sys.argv)>3 else 'd420-staged.json')).read_text())['order'];a=int(sys.argv[1]);limit=int(sys.argv[2]) if len(sys.argv)>2 else 61896
accepted={v['module'] for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
for m in order:
 if m in accepted:continue
 if a>limit:break
 for retry in range(11):
  rc=subprocess.call([sys.executable,str(R/'tools/pv-rjdec-20261028/d420-compile.py'),str(a),'0',m],cwd=R)
  if rc not in [77,78]:break
  if retry==10:raise SystemExit('ten admission refusals; continue compile-free work')
  deadline=time.monotonic()+181
  while time.monotonic()<deadline:time.sleep(min(10,deadline-time.monotonic()))
 if rc:raise SystemExit(rc)
 a+=1
print('NEXT UNUSED ID',a,flush=True)
