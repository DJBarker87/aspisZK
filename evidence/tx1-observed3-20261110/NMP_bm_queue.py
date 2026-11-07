from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for a,m in json.loads((E/sys.argv[1]).read_text()):
 assert not (E/a/'receipt.json').exists(),'Never resubmit '+a
 r=subprocess.run([sys.executable,str(E/'NMP_bm_compile.py'),a,m])
 if r.returncode:raise SystemExit(r.returncode)
