from pathlib import Path
import json,os,subprocess,sys
E=Path(__file__).resolve().parent
q=json.loads((E/'NDB_QUEUE.json').read_text())
start=int(sys.argv[1]); names=sys.argv[2:] or q
for name in names:
 for neg in [False,True]:
  a='NDB_K'+str(start).zfill(3);target='r1_pool_adapter::NDB_native::NDB_'+name
  assert start<=60
  print('SELECT',a,target,'inverse',neg,flush=True)
  r=subprocess.run([sys.executable,str(E/'NDB_run.py'),a,'kani',target],env={**os.environ,**({'NDB_NEGATIVE':'1'} if neg else {})})
  assert r.returncode==0
  rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
  # Stop on compile/setup failure; solver counterexamples/timeouts are evidence.
  if 'VERIFICATION' not in out and 'Timed out' not in out and 'TIMEOUT' not in out:raise SystemExit('REVIEW '+a)
  if neg and rc['exit_status']==0:raise SystemExit('FINDING unexpected inverse pass '+a)
  start+=1
