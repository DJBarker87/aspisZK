"""Sequential adaptive native gates; never run a redundant negative after failure."""
from pathlib import Path
import subprocess,sys,json,os
E=Path(__file__).resolve().parent
plan=json.loads(Path(sys.argv[1]).read_text())
for row in plan:
 a=row['attempt'];p=E/a/'receipt.json'
 if p.exists():continue
 if row.get('positive'):
  positive=E/row['positive']/'receipt.json'
  if not positive.exists() or json.loads(positive.read_text())['exit_status']!=0:
   (E/(a+'-skipped.json')).write_text(json.dumps(dict(reason='positive has no pass; split before matched control',positive=row['positive']))+'\n');continue
 env=os.environ.copy();env['NBZ_EXTRA_SOURCES']=json.dumps(['NBZ_src/crates/aspis-r1-cost-probe/src/'+s for s in row.get('sources',[])])
 r=subprocess.run([sys.executable,str(E/'NBZ_run.py'),a,row['harness']],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout);print(a,r.returncode,r.stdout[-2600:],flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 if row.get('positive') and rc['exit_status']==0:raise SystemExit('VACUITY FINDING '+a)
 if 'error[' in log or 'compilation error' in log:raise SystemExit('own harness compilation failure: repair before proceeding')
