"""Sequential source upload, hash check and existing extraction queue."""
from pathlib import Path
import subprocess,sys,hashlib,datetime,json,time
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';td=root/'tools/pv-cblib-20261027'
def wait_recent():
 records=[]
 for p in list(out.glob('*upload*.log'))+list(out.glob('*/admission-transport.log')):
  try:r=json.loads(p.read_text())
  except ValueError:continue
  if not r.get('allowed',True):records.append(r)
 if records:
  r=max(records,key=lambda x:x['utc']);until=datetime.datetime.fromisoformat(r['utc']).timestamp()+(30 if 'FileNotFoundError' in r.get('error','') else 180)
  while time.time()<until:time.sleep(min(60,until-time.time()))
for i in range(10):
 wait_recent()
 subprocess.run([sys.executable,str(td/'wait_capacity.py')],check=True)
 p=subprocess.run([sys.executable,str(td/'upload_reference.py')])
 if p.returncode==0:break
 if p.returncode!=78:sys.exit(p.returncode)
else:sys.exit(78)
expected=hashlib.sha256((td/'lib.rs').read_bytes()).hexdigest()
actual=subprocess.check_output(['ssh','dombarker@100.108.41.90','sha256sum /home/dombarker/project-offloads/codex-pv-cblib-20261027/source-proof/lib.rs'],text=True).split()[0]
assert actual==expected,(actual,expected)
(out/'resume9-upload-verified.json').write_text(json.dumps({'source_sha256':actual,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()},indent=2)+'\n')
for variant in sys.argv[1:]:
 p=subprocess.run([sys.executable,str(td/'queue_extract.py'),variant,'resume9-verified'])
 if p.returncode:sys.exit(p.returncode)
