from pathlib import Path
import subprocess,sys,json,os
E=Path(__file__).resolve().parent
# Source corrected/uploaded by NBZ_SYNC002 after excluded K025 compilation.
for i,row in enumerate(json.loads((E/'NBZ_WINDOW_PLAN.json').read_text()),27):
 a=f'NBZ_K{i:03d}'
 env=os.environ.copy();env['NBZ_EXTRA_SOURCES']=json.dumps(['NBZ_src/crates/aspis-r1-cost-probe/src/NBZ_windows.rs'])
 r=subprocess.run([sys.executable,str(E/'NBZ_run.py'),a,row['harness']],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout);print(a,r.returncode,r.stdout[-3200:],flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/a/'stdout.log').read_text();rc=json.loads((E/a/'receipt.json').read_text())
 if row['negative'] and rc['exit_status']==0:raise SystemExit('VACUITY: '+a)
 if 'error[' in log:raise SystemExit('repair own harness before next run')
