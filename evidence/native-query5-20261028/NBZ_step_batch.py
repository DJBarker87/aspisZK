from pathlib import Path
import subprocess,sys,json,os
E=Path(__file__).resolve().parent
r=subprocess.run([sys.executable,str(E/'NBZ_sync.py'),'NBZ_SYNC003','NBZ_steps','/tmp/NBZ_steps.rs']);assert r.returncode==0
for i,case in [(35,'raw_word'),(37,'horner'),(39,'finish')]:
 for off,negative in [(0,False),(1,True)]:
  a=f'NBZ_K{i+off:03d}';name='verifier::candidate::NBZ_steps::NBZ_'+case+('_negative' if negative else '')
  env=os.environ.copy();env['NBZ_EXTRA_SOURCES']=json.dumps(['NBZ_src/crates/aspis-r1-cost-probe/src/NBZ_steps.rs','NBZ_src/crates/aspis-r1-cost-probe/src/NBZ_windows.rs'])
  r=subprocess.run([sys.executable,str(E/'NBZ_run.py'),a,name],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (E/(a+'-driver.log')).write_text(r.stdout);print(a,r.returncode,r.stdout[-2700:],flush=True)
  if r.returncode:raise SystemExit(r.returncode)
  rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
  if negative and rc['exit_status']==0:raise SystemExit('VACUITY '+a)
  if not negative and rc['exit_status']!=0:
   (E/(f'NBZ_K{i+1:03d}'+'-skipped.json')).write_text(json.dumps(dict(reason='positive did not pass; split first',positive=a))+'\n');break
  if 'error[' in log:raise SystemExit('repair own compile input')
