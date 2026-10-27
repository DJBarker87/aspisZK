"""Run one authorized small-width link; admission retries are not Kani runs."""
from pathlib import Path
import json,subprocess,datetime,time,sys
root=Path(__file__).resolve().parents[2];td=root/'tools/pv-cblib-20261027';out=root/'evidence/pv-cblib-20261027'
def wait_refusal():
 rows=[]
 for p in list(out.glob('*upload*.log'))+list(out.glob('*/admission-transport.log')):
  try:r=json.loads(p.read_text())
  except ValueError:continue
  if not r.get('allowed',True):rows.append(r)
 for p in out.glob('*/collected-receipt.json'):
  r=json.loads(p.read_text()).get('admissions',{}).get('admission-barrier.json',{})
  if r and not r.get('allowed',True):rows.append(r)
 if rows:
  r=max(rows,key=lambda x:x['utc']);until=datetime.datetime.fromisoformat(r['utc']).timestamp()+(30 if 'FileNotFoundError' in r.get('error','') else 180)
  while time.time()<until:time.sleep(min(60,until-time.time()))
mode=sys.argv[1]
if mode=='upload':
 for i in range(10):
  wait_refusal();subprocess.run([sys.executable,str(td/'wait_capacity.py')],check=True)
  p=subprocess.run([sys.executable,str(td/'upload_kani.py')])
  if p.returncode!=78:sys.exit(p.returncode)
else:
 for i in range(1,11):
  wait_refusal();subprocess.run([sys.executable,str(td/'wait_capacity.py')],check=True)
  p=subprocess.run([sys.executable,str(td/'resume9_kani.py'),f'resume9-{mode}-r{i:02}',f'resume9_links::{mode}','standalone'])
  if p.returncode!=78:sys.exit(p.returncode)
sys.exit(78)
