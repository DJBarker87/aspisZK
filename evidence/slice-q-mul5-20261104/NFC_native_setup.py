from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import shutil,hashlib,json,subprocess,sys
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-q-mul5-20261029'
with (B/'NFC_native_setup_barrier.log').open('w') as f:r=subprocess.run(['python3',str(P/'codex-cx-s2h-20261023/S2H_reservation.py'),str(B/'NFC_native_setup_reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((B/'NFC_native_setup_reservation.json').read_text());print(json.dumps(dict(admission=a,exit=r.returncode)),flush=True)
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(78)
src=P/'codex-cx-slice-q-mul4-20261029/NFA_src';dst=B/'NFC_src'
assert not dst.exists();shutil.copytree(src,dst,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
pins={str(p.relative_to(dst)):hashlib.sha256(p.read_bytes()).hexdigest() for p in dst.rglob('*') if p.is_file() and p.suffix in ['.rs','.toml','.lock']}
(B/'NFC_SOURCE_PINS.json').write_text(json.dumps(pins))
print(json.dumps(dict(source=str(src),destination=str(dst),files=pins)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NFC_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout[:500]+r.stderr
(E/'NFC_NATIVE_SOURCE_IMPORTS.json').write_text(r.stdout.splitlines()[-1]);print('private scratch source copied')
