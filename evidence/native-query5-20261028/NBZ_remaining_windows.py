from pathlib import Path
import subprocess,sys,json,os
E=Path(__file__).resolve().parent
for i,kind in [(29,'weight'),(31,'line'),(33,'inverse')]:
 for off,negative in [(0,False),(1,True)]:
  a=f'NBZ_K{i+off:03d}';name='verifier::candidate::NBZ_windows::NBZ_'+kind+'_window'+('_negative' if negative else '')
  if (E/a/'receipt.json').exists():continue
  env=os.environ.copy();env['NBZ_EXTRA_SOURCES']=json.dumps(['NBZ_src/crates/aspis-r1-cost-probe/src/NBZ_windows.rs'])
  r=subprocess.run([sys.executable,str(E/'NBZ_run.py'),a,name],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (E/(a+'-driver.log')).write_text(r.stdout);print(a,r.returncode,r.stdout[-2700:],flush=True)
  if r.returncode:raise SystemExit(r.returncode)
  rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
  if negative and rc['exit_status']==0:raise SystemExit('VACUITY '+a)
  if not negative and rc['exit_status']!=0:
   (E/(f'NBZ_K{i+1:03d}'+'-skipped.json')).write_text(json.dumps(dict(reason='positive did not pass; split first, no redundant negative shape',positive=a))+'\n');break
