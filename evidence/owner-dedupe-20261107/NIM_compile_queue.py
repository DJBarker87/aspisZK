from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for i,m in enumerate(json.loads((E/'NIM_PROVENANCE.json').read_text())['order'][3:]+['NIM_COMBINED_IMPORT'],11):
 r=subprocess.run([sys.executable,str(E/'NIM_run.py'),f'NIM_L{i:03}','lean',m])
 if r.returncode:sys.exit(r.returncode)
