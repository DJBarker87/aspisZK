from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(32,'slice_fidelity_contract',{}),(37,'slice_fidelity_contract',{'NKK_INVERT':'1'}),(38,'slice_fidelity_real',{}),(39,'slice_fidelity_unimplied',{}),(40,'slice_fidelity_modifies_check',{}),(41,'slice_fidelity_modifies_check',{'NKK_BAD_REPLY':'1'}),(42,'proof_digest_frame_contract',{}),(46,'proof_digest_frame_contract',{'NKK_INVERT':'1'}),(47,'proof_digest_frame_contract',{'NKK_BAD_REPLY':'1'}),(33,'public_digest_stage',{}),(34,'public_digest_stage',{'NKK_INVERT':'1'}),(35,'checkpoint_digest_stage',{}),(36,'checkpoint_digest_stage',{'NKK_INVERT':'1'}),(43,'pair_owned_window',{}),(44,'pair_owned_window',{'NKK_INVERT':'1'}),(45,'pair_owned_window',{'NKK_BAD_ALLOC':'1'})]
for a,t,env in jobs:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_K{a:03}','kani','verifier::NKK_parent::'+t],env={**os.environ,**env})
 p=E/f'NKK_K{a:03}'/'receipt.json'
 if not p.exists():break
 out=p.with_name('stdout.log').read_text();fail=bool(env) or t=='slice_fidelity_unimplied'
 if (r.returncode==0)==fail or (fail and 'VERIFICATION:- FAILED' not in out) or 'timed out' in out.lower():break
