"""Owned serial queue; stops on any unexpected verdict or incomplete control."""
from pathlib import Path
import subprocess,json,sys,os
E=Path(__file__).resolve().parent
for job in json.loads((E/sys.argv[1]).read_text()):
 a,kind,target=job['attempt'],job['kind'],job['target'];env=os.environ.copy();env.update(job.get('env',{}))
 r=subprocess.run([sys.executable,str(E/'NHU_run.py'),a,kind,target],env=env)
 if r.returncode!=job.get('exit',0):sys.exit(r.returncode or 99)
 if job.get('control'):
  log=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- FAILED' in log and 'Failed Checks:'in log and 'timed out'not in log.lower() and 'memory exhausted'not in log.lower()
 print('NHU_QUEUE_DONE '+a,flush=True)
