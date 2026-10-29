from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(59,'NEA_copy::KMX_checks::KMX_ptr_correct','',0),(60,'NEA_copy::KMX_checks::KMX_ptr_wrong','',1),(61,'NEA_copy::KMX_checks::KMX_ptr_correct','NEA_fold',0),(62,'NEA_copy::KMX_checks::KMX_ptr_wrong','NEA_fold',1)]
for start,name in [(63,'bm_repeat'),(65,'em_repeat'),(67,'sm_repeat'),(69,'em_pair'),(71,'sm_pair'),(73,'bm_pair'),(75,'em_full'),(77,'sm_full'),(79,'bm_full')]:
 jobs += [(start,'verifier::NEA_fold::'+name,'',0),(start+1,'verifier::NEA_fold::'+name,'NEA_wrong_log',1)]
rows=[]
for k,target,cfg,expected in jobs:
 a=f'NEA_K{k:03d}';env=dict(os.environ);env.pop('NEA_ROOT',None);env.pop('NEA_RUST_CFG',None)
 if cfg:env['NEA_RUST_CFG']=cfg
 r=subprocess.run(['python3',str(E/'NEA_run.py'),a,'kani',target],env=env)
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 timeout='timed out' in log.lower() or rc['exit_status'] in [124,137]
 good=rc['exit_status']==expected and not timeout and ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log and 'error: could not compile' not in log
 row=dict(attempt=a,target=target,cfg=cfg,expected=expected,exit=rc['exit_status'],timeout=timeout,expected_verification_verdict=good);rows.append(row)
 (E/'NEA_LOG_CONTROL_RUNS.json').write_text(json.dumps(rows,indent=2)+'\n')
 print('CHECK',json.dumps(row),flush=True)
 if timeout:
  # Own solver temporary files only. Do not resubmit or increase timeout.
  subprocess.run(['python3',str(E/'NEA_recover_sources.py')],check=True)
 elif not good:raise SystemExit('Unexpected verdict; isolate this own input before continuing')
