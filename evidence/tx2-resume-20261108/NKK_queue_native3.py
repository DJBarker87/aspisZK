from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(22,'owned_tail_stage',{}),(23,'owned_tail_stage',{'NKK_INVERT':'1'}),(24,'owned_tail_stage',{'NKK_BAD_DROP':'1'}),(25,'semantic_writeback_stage',{}),(26,'semantic_writeback_stage',{'NKK_INVERT':'1'}),(27,'semantic_writeback_stage',{'NKK_BAD_VIEW':'1'}),(28,'header_prefix_stage',{}),(29,'header_prefix_stage',{'NKK_INVERT':'1'}),(30,'header_prefix_stage',{'NKK_BAD_BACKING':'1'}),(31,'proof_digest_stage',{}),(32,'proof_digest_stage',{'NKK_INVERT':'1'}),(33,'public_digest_stage',{}),(34,'public_digest_stage',{'NKK_INVERT':'1'}),(35,'checkpoint_digest_stage',{}),(36,'checkpoint_digest_stage',{'NKK_INVERT':'1'}),(37,'pair_scalar_window',{}),(38,'pair_scalar_window',{'NKK_INVERT':'1'}),(39,'pair_scalar_window',{'NKK_BAD_ALLOC':'1'}),(40,'pair_array_window',{}),(41,'pair_array_window',{'NKK_INVERT':'1'}),(42,'pair_array_window',{'NKK_BAD_ALLOC':'1'}),(43,'pair_owned_window',{}),(44,'pair_owned_window',{'NKK_INVERT':'1'}),(45,'pair_owned_window',{'NKK_BAD_ALLOC':'1'})]
for a,t,env in jobs:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_K{a:03}','kani','verifier::NKK_parent::'+t],env={**os.environ,**env})
 p=E/f'NKK_K{a:03}'/'receipt.json'
 if not p.exists():break
 out=p.with_name('stdout.log').read_text()
 if (r.returncode==0)==bool(env) or (env and 'VERIFICATION:- FAILED' not in out) or 'timed out' in out.lower():break
