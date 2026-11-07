from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for i,m in enumerate(json.loads((E/'NNG_TRANSPORT_TYPES.json').read_text())['modules'],6):
 a=f'NNG_L{i:03}'
 assert not (E/a/'receipt.json').exists()
 r=subprocess.run([sys.executable,str(E/'NNG_compile.py'),a,m])
 if r.returncode:raise SystemExit(r.returncode)
