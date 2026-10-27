from pathlib import Path
import subprocess,json,sys
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume5'
manifest=json.loads((e/'owned-source-manifest.json').read_text())['targets']
start=int(sys.argv[1]);offset=int(sys.argv[2]) if len(sys.argv)>2 else 0
for module in manifest[offset:]:
 p=subprocess.run([sys.executable,str(r/'tools/pv-join-20261026/host-check5.py'),str(start),module],cwd=r)
 if p.returncode:raise SystemExit(p.returncode)
 start+=1
