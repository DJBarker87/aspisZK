from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=json.loads((E/'NBH_BATCH2_JOBS.json').read_text())
# Leave the final ASR8 gate until after the formal audit; stop at Kani30.
for a,h in jobs[:10]:
 assert not (E/a/'receipt.json').exists(),a
 r=subprocess.run(['python3',str(E/'NBH_native.py'),'run',a,h])
 if r.returncode:sys.exit(r.returncode)
