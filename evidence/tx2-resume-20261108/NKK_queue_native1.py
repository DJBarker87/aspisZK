from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[('K005','query_chunk8',{'NKK_BAD_BACKING':'1'}),('K006','query_chunk6',{}),('K007','query_chunk6',{'NKK_INVERT':'1'}),('K008','query_chunk6',{'NKK_BAD_BACKING':'1'}),('K009','state_roots_stage',{}),('K010','state_roots_stage',{'NKK_INVERT':'1'}),('K011','state_roots_stage',{'NKK_BAD_BACKING':'1'}),('K012','gamma_stage',{}),('K013','gamma_stage',{'NKK_INVERT':'1'}),('K014','gamma_stage',{'NKK_BAD_BACKING':'1'}),('K015','z_claim_stage',{}),('K016','z_claim_stage',{'NKK_INVERT':'1'}),('K017','z_claim_stage',{'NKK_BAD_BACKING':'1'})]
for a,t,env in jobs:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),'NKK_'+a,'kani','verifier::NKK_parent::'+t],env={**os.environ,**env})
 receipt=E/('NKK_'+a)/'receipt.json'
 if not receipt.exists():break
 out=(receipt.parent/'stdout.log').read_text()
 expected_fail=bool(env)
 if (r.returncode==0)==expected_fail or (expected_fail and 'VERIFICATION:- FAILED' not in out) or 'timed out' in out.lower():break
