from pathlib import Path
import os,subprocess,json
E=Path(__file__).resolve().parent
for k,target,cfg,expected in [(53,'verifier::NEA_fold::linear_add','NEA_wrong_linear',1),(54,'verifier::NEA_fold::linear_sub','',0),(55,'verifier::NEA_fold::linear_sub','NEA_wrong_linear',1)]:
 a=f'NEA_K{k:03d}';env=dict(os.environ);env.pop('NEA_ROOT',None);env.pop('NEA_RUST_CFG',None)
 if cfg:env['NEA_RUST_CFG']=cfg
 r=subprocess.run(['python3',str(E/'NEA_run.py'),a,'kani',target],env=env)
 assert r.returncode==0
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 assert rc['exit_status']==expected and 'timed out' not in log.lower()
 assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log
 assert 'error: could not compile' not in log
 print('validated',a,flush=True)
