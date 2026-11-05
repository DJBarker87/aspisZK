"""Serial focused compile queue; stop on the first nonzero receipt."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);targets=sys.argv[2:]
for number,target in enumerate(targets,start):
 a=f'NIO_L{number:03d}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIO_run.py'),a,'lean',target],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+a+'; inspect client; never resubmit blindly')
 d=json.loads(p.read_text());print(a+' '+target+' exit '+str(d['exit_status']),flush=True)
 if d['exit_status']:raise SystemExit('Repair or split changed target before continuing')
