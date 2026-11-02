"""Focused source only, library object pins before compilation, no dependency build."""
from pathlib import Path
import subprocess,json,os,hashlib,sys
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=subprocess.run(['lake','env','printenv','LEAN_PATH'],capture_output=True,text=True,cwd=B)
assert r.returncode==0,r.stderr
roots=[Path(p) for p in r.stdout.strip().split(':') if p]
pins={}
for root in roots:
 for dirname in ['Aeneas','Aeneas.olean']:
  p=root/dirname
  if p.is_file():pins[str(p)]=sha(p)
  elif p.is_dir():
   for q in sorted(p.rglob('*.olean')):pins[str(q)]=sha(q)
(B/'NEK_L001_LIBRARY_PINS.json').write_text(json.dumps(dict(LEAN_PATH=r.stdout.strip(),aeneas_object_hashes=pins,note='new theorem imports only Lean Init; pin every Aeneas object the selected path can resolve anyway'),indent=2)+'\n')
print('Aeneas object pins',len(pins),flush=True)
rc=subprocess.run(['lake','env','lean','-j1','-M7000','-DElab.async=false','NEK_ByteWindows.lean'],cwd=B).returncode
sys.exit(rc)
