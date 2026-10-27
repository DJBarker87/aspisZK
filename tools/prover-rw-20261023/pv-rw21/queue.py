"""Serial focused launcher. Reservation retries always use a fresh ID after >=180s.
Stops on a charged failure, missing dependency, ten refusals, or focused budget end.
"""
from pathlib import Path
import datetime,json,subprocess,sys,time
r=Path(__file__).resolve().parents[3]
e=r/'evidence/pv-rw21-20261027'
for module in sys.argv[1:]:
 for retry in range(10):
  rows=[json.loads(p.read_text()) for p in e.glob('37???-input.json')]
  refused=[x for x in rows if x.get('preflight_exit')==78]
  if refused:
   latest=max(datetime.datetime.fromisoformat(x['utc']).timestamp() for x in refused)
   until=latest+182
   while time.time()<until: time.sleep(min(30,until-time.time()))
  charged=sum(json.loads(p.read_text()).get('charged',False) for p in e.glob('37???-receipt.json'))
  if charged>=97: raise SystemExit('Focused budget complete; preserve final three audit attempts')
  attempt=max([x['attempt'] for x in rows]+[37699])+1
  result=subprocess.run([sys.executable,str(Path(__file__).with_name('attempt.py')),str(attempt),module],cwd=r)
  if result.returncode==0: break
  receipt=e/f'{attempt}-receipt.json'
  if receipt.exists() and json.loads(receipt.read_text()).get('charged'): raise SystemExit(result.returncode)
  record=json.loads((e/f'{attempt}-input.json').read_text())
  if record.get('preflight_exit')!=78: raise SystemExit(result.returncode)
 else: raise SystemExit('Ten reservation refusals; switch to compile-free work')
