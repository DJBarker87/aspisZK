from pathlib import Path
import subprocess
T=Path(__file__).parent
for num,name in enumerate(['S2F_proof_decision','S2F_distinct','S2F_readonly','S2F_cp_metadata'],18):
 r=subprocess.run(['python3',str(T/'S2F_attempt.py'),'kani',str(num),name])
 if r.returncode: raise SystemExit(r.returncode)
