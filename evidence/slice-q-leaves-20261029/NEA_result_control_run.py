from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(41,'r0::domain::NEA_domain::constructor','NEA_wrong_index',1),(42,'r0::domain::NEA_result_controls::weak_contract','',0),(43,'r0::domain::NEA_result_controls::weak_contract','NEA_wrong_weak',1),(44,'r0::domain::NEA_result_controls::real_caller','',0),(45,'r0::domain::NEA_result_controls::replacement_caller','',1),(46,'r0::domain::NEA_result_controls::frame_contract','',0),(47,'r0::domain::NEA_result_controls::frame_contract','NEA_wrong_frame',1),(48,'NEA_copy::KMX_checks::KMX_ptr_correct','',0),(49,'NEA_copy::KMX_checks::KMX_ptr_wrong','',1)]
rows=[]
for k,target,cfg,expected in jobs:
 a=f'NEA_K{k:03d}';env=dict(os.environ,NEA_ROOT='core');env.pop('NEA_RUST_CFG',None)
 if cfg:env['NEA_RUST_CFG']=cfg
 r=subprocess.run(['python3',str(E/'NEA_run.py'),a,'kani',target],env=env)
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 row={'attempt':a,'target':target,'expected':expected,'exit':rc['exit_status'],'cfg':cfg,'timeout':'timed out' in log.lower() or rc['exit_status'] in [124,137]};rows.append(row)
 (E/'NEA_RESULT_CONTROL_RUNS.json').write_text(json.dumps(rows,indent=2)+'\n')
 print('CONTROL',json.dumps(row),flush=True)
 if row['timeout'] or rc['exit_status']!=expected or (expected==1 and ('VERIFICATION:- FAILED' not in log or 'error: could not compile' in log)):raise SystemExit('Stop unexpected control verdict; isolate before continuing')
