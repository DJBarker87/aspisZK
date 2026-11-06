from pathlib import Path
import subprocess,time
E=Path(__file__).resolve().parent
# Wait only on this job's serial client; no host scope is opened by this wait.
while (E/'NJR_CLIENT_ACTIVE').exists():time.sleep(1)
for a,target in [('NJR_L035','NJR_DecodedWords')]:
 r=subprocess.run(['python3',str(E/'NJR_run.py'),a,'lean',target])
 if r.returncode:break
