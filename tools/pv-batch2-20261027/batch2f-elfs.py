"""Run existing SBF launcher sequentially, preserving all keys and refusal evidence."""
from pathlib import Path
import datetime,json,subprocess,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');W=H/'candidate';prefix=sys.argv[1] if len(sys.argv)>1 else 'batch2f-box'
for mode in ['default','devnet','pool']:
 for n in range(1,11):
  label=f'{prefix}-{mode}-{n:03}';out=W/label
  if out.exists():raise SystemExit('existing receipt: recover read-only; never resubmit '+label)
  print('SBF target',mode,'attempt',n,'expected work: optimized compilation only; caps6G/8G,swap0,Tasks64',flush=True)
  status=subprocess.run(['python3',str(H/'build.py'),'candidate',mode,label]).returncode
  if status==0:break
  if status!=78:raise SystemExit(status)
  br=out/'admission-barrier.json';rr=out/'reservation.json'
  r=json.loads((br if br.exists() else rr).read_text())
  if r.get('error'):raise SystemExit('barrier error; inspect p_prime before further launch: '+r['error'])
  assert r.get('allowed') is False
  stamp=datetime.datetime.fromisoformat(r['utc']).timestamp()
  print(label,'uncharged ordinary reservation hold; cooldown to',stamp+180,flush=True)
  while time.time()<stamp+180:time.sleep(min(55,stamp+180-time.time()+0.1))
 else:raise SystemExit('ten resource holds for '+mode+'; compile-free review required')
print('all three ELF pins match',flush=True)
