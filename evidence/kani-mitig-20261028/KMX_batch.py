from pathlib import Path
import sys,subprocess,json,re
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);patterns=sys.argv[2:]
for i,pattern in enumerate(patterns,start):
 a=f'KMX_K{i:03}'
 r=subprocess.run([sys.executable,str(E/'KMX_run.py'),a,'kani','python3','KMX_gate.py',a,pattern,'--cbmc-args','--unwinding-assertions'])
 if r.returncode:raise SystemExit(r.returncode)
 text=(E/a/'stdout.log').read_text()
 if 'Checking harness' not in text:raise SystemExit('STOP no verification result '+a)
