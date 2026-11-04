from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-parser2-20261105';H='dombarker@100.108.41.90'
code=f'''from pathlib import Path
import hashlib,json,subprocess,sys
b=Path({B!r});p=b/'NGO_AUDIT_SETUP-admission.json'
with (b/'NGO_AUDIT_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/JFz_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
if r.returncode or not p.exists() or json.loads(p.read_text()).get('allowed') is not True:print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode or 78)
result={{'admission':json.loads(p.read_text()),'copied':{{}}}}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 src=Path('/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104/NFQ_native')/n;dst=b/'NGO_native'/n;dst.parent.mkdir(exist_ok=True);dst.write_bytes(src.read_bytes());result['copied'][n]={{'source':str(src),'sha256':hashlib.sha256(dst.read_bytes()).hexdigest(),'bytes':dst.stat().st_size}}
print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True);(E/'NGO_AUDIT_SETUP.json').write_text(r.stdout);assert r.returncode==0,r.stdout+r.stderr
