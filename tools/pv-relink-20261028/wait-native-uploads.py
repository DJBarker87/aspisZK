"""Wait for admission; preparation only, never starts a compiler or bypasses a refusal."""
from pathlib import Path
import subprocess,time,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028'
for i in range(3,13):
 # The previous upload refusal is at04:05:27; this script starts after its wait.
 label=f'std-inputs-r{i}'
 r=subprocess.run(['python3',str(R/'tools/pv-relink-20261028/upload.py'),label,*[f'tools/pv-relink-20261028/{f}' for f in ['v178.rs','v179.rs','v182.rs','run-std.sh','run-std-all.sh','run-cargo-all.sh']]])
 if r.returncode==0:print('UPLOADS READY',flush=True);break
 a=json.loads((E/f'upload-{label}.json').read_text())
 if a.get('allowed') is True:raise SystemExit(r.returncode)
 print('ADMISSION REFUSED; next retry in180s',i,a.get('utc'),flush=True)
 time.sleep(180)
else:raise SystemExit(78)
