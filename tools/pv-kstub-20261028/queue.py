from pathlib import Path
import subprocess,json,time,sys,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';D='/home/dombarker/project-offloads/codex-pv-kstub-20261028';H='dombarker@100.108.41.90'
p=json.loads((E/'plans.json').read_text());runid=1
for plan in p:
 if (E/(plan['row']+'-finding.json')).exists():continue
 for negative in [False,True]:
  runid+=1;name=f'K{runid:02}';h=plan['negative'] if negative else plan['harness']
  prefix=('checks::' if plan['package']=='cb' else {'join_one_byte':'join_split::','string_path':'split_checks::','string_push':'split_checks::','join_two':'resume8_links::','push_bytes':'resume8_links::','join_slices_two':'resume9_links::'}.get(plan['harness'],'') if plan['package']=='cblib' else 'field::wide_exact::pv_cb3_arbitrary_bytes::' if plan['package']=='native/core' else 'sealed::pv_alib_checks::' if plan['package']=='split' else '')
  h=prefix+h
  cmd=['timeout','900','taskset','--cpu-list','0-3','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','CARGO_PROFILE_DEV_OPT_LEVEL=3',f'TMPDIR={D}/tmp-Kani',f'CARGO_TARGET_DIR={D}/target','cargo','kani','--manifest-path',D+'/'+plan['package']+'/Cargo.toml','--lib','--exact','--harness',h,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','4','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions','--slice-formula']
  existing=(E/name/'receipt.json').exists()
  if not existing:(E/(name+'-target.json')).write_text(json.dumps(dict(**plan,negative_control=negative,command=cmd),indent=2))
  if not existing:
   for transport_attempt in range(11):
    frozen=subprocess.run(['ssh',H,shlex.join(['python3',D+'/freeze-inputs.py',name,plan['package']])],text=True,capture_output=True)
    if frozen.returncode!=255:break
    with (E/'freeze-transport-history.jsonl').open('a') as history:history.write(json.dumps(dict(run=name,exit=255,stderr=frozen.stderr,time=time.time(),attempt=transport_attempt))+'\n')
    if transport_attempt<10:time.sleep(60)
   if frozen.returncode:sys.exit('Source-freeze transport/setup failed; no compiler submitted')
   aggregate_refusals=0
   while True:
    q=subprocess.run([sys.executable,str(R/'tools/pv-kstub-20261028/scope.py'),name,'Kani',*cmd])
    if q.returncode==79:time.sleep(60);continue
    if q.returncode!=78:break
    if aggregate_refusals>=10:break
    aggregate_refusals+=1;time.sleep(180)
  f=E/name/'receipt.json'
  if not f.exists():
   if q.returncode==78:print('UNCHARGED retry block exhausted; do compile-free review, wait180s, then return to this unlaunched target');sys.exit(78)
   sys.exit('Result unresolved; recover submitted scope before any resubmission')
  receipt=json.loads(f.read_text());log=(E/name/'output.log').read_text()
  status='TIMEOUT' if receipt['exit']==124 else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log or 'VERIFICATION: SUCCESSFUL' in log else 'FAIL' if 'VERIFICATION:- FAILED' in log or 'VERIFICATION: FAILED' in log else 'ERROR'
  outcome=dict(**plan,run=name,negative_control=negative,status=status,receipt=str(f.relative_to(R)))
  (E/(name+'-result.json')).write_text(json.dumps(outcome,indent=2))
  if status=='ERROR':sys.exit('Compile/setup error; repair inputs before continuing')
  if (not negative and status=='FAIL') or (negative and status=='PASS'):
   (E/(plan['row']+'-finding.json')).write_text(json.dumps(outcome,indent=2));break
