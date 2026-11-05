from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-parser3-20261105';H='dombarker@100.108.41.90'
code=f'''from pathlib import Path
import hashlib,json,subprocess,sys
b=Path({B!r});p=b/'NGV_AUDIT_SETUP-admission.json'
with (b/'NGV_AUDIT_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/JFz_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
if r.returncode or not p.exists() or json.loads(p.read_text()).get('allowed') is not True:print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode or 78)
result={{'admission':json.loads(p.read_text()),'copied':{{}}}}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 src=Path('/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104/NFQ_native')/n;dst=b/'NGV_native'/n;dst.parent.mkdir(exist_ok=True);dst.write_bytes(src.read_bytes());result['copied'][n]={{'source':str(src),'sha256':hashlib.sha256(dst.read_bytes()).hexdigest(),'bytes':dst.stat().st_size}}
print(json.dumps(result))
'''
for retry in range(1,11):
 time.sleep(180)
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 (E/f'NGV_AUDIT_SETUP-retry-{retry}.json').write_text(r.stdout)
 try:result=json.loads(r.stdout)
 except json.JSONDecodeError:raise RuntimeError(r.stderr)
 if r.returncode==0 and result.get('admission',{}).get('allowed') is True:
  (E/'NGV_AUDIT_SETUP.json').write_text(r.stdout);print('audit support admitted and copied');break
 assert result.get('allowed') is False or r.returncode==78,'Infrastructure failure'
 print('audit support reservation refused; wait and retry',flush=True)
else:raise RuntimeError('Admission retries exhausted')
