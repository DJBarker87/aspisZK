from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for row in json.loads((E/'NBZ_CONTROL_PLAN.json').read_text()):
 a=row['attempt']
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'NBZ_run.py'),a,row['harness']],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout)
 print(a,r.returncode,r.stdout[-3000:],flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 if rc['exit_status']==0:raise SystemExit('VACUITY FINDING: negative control PASSED '+a)
 if 'Failed Checks:' not in log or 'CBMC timed out' in log or rc['exit_status'] != 1:
  print('Review non-proof failure before proceeding',flush=True);raise SystemExit(2)
