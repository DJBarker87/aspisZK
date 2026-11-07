from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import shutil,hashlib,json
s=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NMQ_20261111/NMQ_native/NMQ_ProofDriver');d=Path('/home/dombarker/project-offloads/codex-cx-libc-20261111/LIBC_native/LIBC_ProofDriver');d.parent.mkdir(exist_ok=True)
if d.exists():assert d.read_bytes()==s.read_bytes()
else:shutil.copy2(s,d)
print(json.dumps({'source':str(s),'destination':str(d),'sha256':hashlib.sha256(d.read_bytes()).hexdigest(),'bytes':d.stat().st_size,'reuse':'unchanged optimized ledger25 raw ax2 driver; no new native code or extractor'}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'LIBC_DRIVER_PIN.json').write_text(r.stdout)
print('Pinned unchanged ledger25 driver')
