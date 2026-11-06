from pathlib import Path
import json,shutil,hashlib,subprocess
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-verify-observed5-20261107')
pins=json.loads((B/'NJG_INPUT_PINS.json').read_text())
for n,h in pins.items():
 p=P/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h,(n,'input mismatch');shutil.copyfile(p,B/n)
r=subprocess.run(['python3','NJG_stage.py','--check','--workspace','NJG_src','--out','NJG_preflight'],cwd=B);assert r.returncode==0
r=subprocess.run(['git','apply',str(B/'NJG_KMX.patch')],cwd=B/'NJG_src',capture_output=True,text=True);assert r.returncode==0,r.stderr
(B/'NJG_SETUP.json').write_text(json.dumps(dict(inputs=pins,kmx_patch_sha256=hashlib.sha256((B/'NJG_KMX.patch').read_bytes()).hexdigest(),source_bytes=sum(p.stat().st_size for p in (B/'NJG_src').rglob('*') if p.is_file()),cargo_target_dir=str(B/'NJG_target')),indent=2))
print('NJG frozen graph checked and exact KMX applied')
