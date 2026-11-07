from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for n,h in [(2,'NMO_rounds_reply_control'),(3,'NMO_rounds_argument_control'),(4,'NMO_rounds_footprint_control'),(5,'NMO_copy_control')]:
 a=f'NMO_K{n:03}';subprocess.run([sys.executable,str(E/'NMO_kconfig.py'),a,'r1_semantic::NMO_finish::'+h],check=True)
 subprocess.run([sys.executable,str(E/'NMO_run.py'),a])
 p=E/a/'receipt.json';assert p.exists(),'Recover read-only; no further scope'
 x=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();assert x['exit_status']==1 and 'VERIFICATION:- FAILED' in log and 'timed out'not in log,'Review control verdict before proceeding'
print('All initial-branch controls failed as required')
