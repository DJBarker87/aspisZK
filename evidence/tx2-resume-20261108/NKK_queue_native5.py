from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(34,'public_digest_stage',{}),(35,'public_digest_stage',{'NKK_INVERT':'1'}),(36,'checkpoint_digest_stage',{}),(43,'checkpoint_digest_stage',{'NKK_INVERT':'1'}),(44,'checkpoint_digest_stage',{'NKK_BAD_VIEW':'1'}),(45,'pair_owned_window',{}),(48,'pair_owned_window',{'NKK_INVERT':'1'}),(49,'pair_owned_window',{'NKK_BAD_ALLOC':'1'})]
for a,t,env in jobs:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_K{a:03}','kani','verifier::NKK_parent::'+t],env={**os.environ,**env})
 p=E/f'NKK_K{a:03}'/'receipt.json'
 if not p.exists():break
 out=p.with_name('stdout.log').read_text();fail=bool(env)
 if (r.returncode==0)==fail or (fail and 'VERIFICATION:- FAILED' not in out) or 'timed out' in out.lower():break
