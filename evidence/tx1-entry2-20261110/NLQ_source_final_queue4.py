from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(130,'NLQ_Stage1CopyPost'),(132,'NLQ_MetadataFlags'),(133,'NLQ_MetadataBorrow')]
for n,module in jobs:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{n:03d}','lean',module],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1]if r.stdout.strip()else module+': no receipt',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
