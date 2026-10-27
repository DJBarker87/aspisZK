"""Serial job-owned driver. Each invocation performs fresh frozen graph admission."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for number,name in [(1,'c_parent16_left'),(2,'c_parent16_right'),(3,'c_parent32_middle'),(4,'q_owned16'),(5,'q_parent32_left'),(6,'q_parent32_right'),(7,'q_parent32_middle'),(8,'q_parent48_middle'),(9,'q_parent48_right')]:
 a=f'LPi_K{number+1:03d}'
 r=subprocess.run([sys.executable,str(E/'LPi_run.py'),a,name])
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text())
 if rc['exit_status']!=0:raise SystemExit('STOP nonpass '+a+'; inspect before adaptive split')
