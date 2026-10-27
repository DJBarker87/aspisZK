"""Sequential capped extraction through existing admission/barrier scripts."""
from pathlib import Path
import subprocess,time,json,sys,datetime
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';variant=sys.argv[1];label=sys.argv[2]
def latest_refusal():
 rows=[]
 for p in out.glob('*/admission-transport.log'):
  try:r=json.loads(p.read_text())
  except ValueError:continue
  if not r.get('allowed',True):rows.append(r)
 for p in out.glob('*/collected-receipt.json'):
  r=json.loads(p.read_text()).get('admissions',{}).get('admission-barrier.json',{})
  if r and not r.get('allowed',True):rows.append(r)
 for p in out.glob('*-refusal.json'):
  r=json.loads(p.read_text())
  try:r=json.loads(r.get('output',r.get('reason','')))
  except ValueError:continue
  if 'utc' in r:rows.append(r)
 return max(rows,key=lambda r:r['utc']) if rows else None
def wait_refusal():
 r=latest_refusal()
 if not r:return
 delay=30 if 'FileNotFoundError' in r.get('error','') else 180
 until=datetime.datetime.fromisoformat(r['utc']).timestamp()+delay
 while time.time()<until:time.sleep(min(60,until-time.time()))
if __name__ == "__main__":
 for stage in ['charon','aeneas']:
  for i in range(1,11):
   wait_refusal();tag=f'{label}-{i:02}'
   p=subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/extract.py'),stage,variant,tag])
   if p.returncode==0:break
   if p.returncode!=78:sys.exit(p.returncode)
  else:sys.exit(78)
