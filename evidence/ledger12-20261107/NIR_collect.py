from pathlib import Path
import subprocess,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-ledger12-20261107'
for n in ['NIR_CLOSURE_PINS.json.xz','NIR_CLOSURE_PINS.json.sha256','NIR_EXPORT.json']:
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','cat '+B+'/'+n],capture_output=True)
  if r.returncode==0:break
  if r.returncode==255 and retry<10:time.sleep(60);continue
  raise RuntimeError(str(r.stderr))
 (E/n).write_bytes(r.stdout)
print('NIR closure and export receipts recovered read-only')
