from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(13,'gamma_stage',{}),(14,'gamma_stage',{'NKK_INVERT':'1'}),(15,'gamma_stage',{'NKK_BAD_BACKING':'1'}),(16,'z_claim_stage',{}),(17,'z_claim_stage',{'NKK_INVERT':'1'}),(18,'z_claim_stage',{'NKK_BAD_BACKING':'1'}),(19,'semantic_writeback_stage',{}),(20,'semantic_writeback_stage',{'NKK_INVERT':'1'}),(21,'semantic_writeback_stage',{'NKK_BAD_BACKING':'1'}),(22,'owned_tail_stage',{}),(23,'owned_tail_stage',{'NKK_INVERT':'1'}),(24,'owned_tail_stage',{'NKK_BAD_DROP':'1'})]
for a,t,env in jobs:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_K{a:03}','kani','verifier::NKK_parent::'+t],env={**os.environ,**env})
 p=E/f'NKK_K{a:03}'/'receipt.json'
 if not p.exists():break
 out=p.with_name('stdout.log').read_text()
 if (r.returncode==0)==bool(env) or (env and 'VERIFICATION:- FAILED' not in out) or 'timed out' in out.lower():break
