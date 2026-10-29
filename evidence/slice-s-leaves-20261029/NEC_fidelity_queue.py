"""Five serial, same-name Result<Box<After>,Error> fidelity controls required by ruling (t)."""
from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent;num=int(sys.argv[1])
plans=[('contract',{},'NEC_fidelity::shape_contract',0),('inverted_ensures',{'NEC_FIDELITY_INVERT':'1'},'NEC_fidelity::shape_contract',1),('real_unimplied_caller',{},'NEC_fidelity::shape_client',0),('stub_unimplied_caller',{'NEC_FIDELITY_STUB':'1'},'NEC_fidelity::shape_client',1),('modifies_violation',{'NEC_FIDELITY_BAD_MODIFIES':'1'},'NEC_fidelity::shape_contract',1)]
for label,settings,target,wanted in plans:
 a=f'NEC_K{num:03d}';num+=1
 env={k:v for k,v in os.environ.items() if not k.startswith('NEC_')};env.update(NEC_FIDELITY='1',**settings)
 r=subprocess.run([sys.executable,str(E/'NEC_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 if r.returncode:print(r.stdout[-1000:]+r.stderr[-1600:],flush=True);raise SystemExit(r.returncode)
 receipt=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 good=(wanted==0 and receipt['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log) or (wanted==1 and receipt['exit_status']==1 and 'Failed Checks:' in log and 'timed out' not in log.lower())
 row=dict(attempt=a,label=label,target=target,settings=settings,expected_exit=wanted,exit_status=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],admissible=good)
 with (E/'NEC_FIDELITY.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if not good:print('STOP this fidelity shape; no new substitution credit; no unchanged retry.',flush=True);break
print('next attempt',num,flush=True)
