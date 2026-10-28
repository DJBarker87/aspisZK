from pathlib import Path
import subprocess,json,time,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';D='/home/dombarker/project-offloads/codex-pv-kstub-20261028';H='dombarker@100.108.41.90'
p=json.loads((E/'plans.json').read_text());runid=0
for plan in p:
 if (E/(plan['row']+'-finding.json')).exists():continue
 for negative in [False,True]:
  runid+=1;name=f'K{runid:02}';h=plan['negative'] if negative else plan['harness']
  cmd=['timeout','900','taskset','--cpu-list','0-3','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','CARGO_PROFILE_DEV_OPT_LEVEL=3',f'CARGO_TARGET_DIR={D}/target','cargo','kani','--manifest-path',D+'/'+plan['package']+'/Cargo.toml','--lib','--harness',h,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','4','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions','--slice-formula']
  if (E/name/'receipt.json').exists():continue
  (E/(name+'-target.json')).write_text(json.dumps(dict(**plan,negative_control=negative,command=cmd),indent=2))
  for trial in range(11):
   q=subprocess.run([sys.executable,str(R/'tools/pv-kstub-20261028/scope.py'),name,'Kani',*cmd])
   if q.returncode!=78:break
   if trial<10:time.sleep(180)
  f=E/name/'receipt.json'
  if not f.exists():sys.exit('No receipt; infrastructure stop')
  receipt=json.loads(f.read_text());log=(E/name/'output.log').read_text()
  status='TIMEOUT' if receipt['exit']==124 else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log or 'VERIFICATION: SUCCESSFUL' in log else 'FAIL' if 'VERIFICATION:- FAILED' in log or 'VERIFICATION: FAILED' in log else 'ERROR'
  outcome=dict(**plan,run=name,negative_control=negative,status=status,receipt=str(f.relative_to(R)))
  (E/(name+'-result.json')).write_text(json.dumps(outcome,indent=2))
  if status=='ERROR':sys.exit('Compile/setup error; repair inputs before continuing')
  if (not negative and status=='FAIL') or (negative and status=='PASS'):
   (E/(plan['row']+'-finding.json')).write_text(json.dumps(outcome,indent=2));break
