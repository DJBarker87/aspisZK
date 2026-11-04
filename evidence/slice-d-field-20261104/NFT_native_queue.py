"""Serial independent native gates; stop on every unexpected outcome."""
from pathlib import Path
import os,subprocess,json
E=Path(__file__).resolve().parent
jobs=[(16, 'field::NFT_field::cm_frame_window', False, 0), (17, 'field::NFT_field::cm_frame_window', True, 1), (18, 'field::NFT_field::qm_frame_window', False, 0), (19, 'field::NFT_field::qm_frame_window', True, 1), (20, 'field::NFT_square::square_log', False, 0), (21, 'field::NFT_square::square_log', True, 1), (22, 'field::NFT_square::copy_cm_positive', False, 0), (23, 'field::NFT_square::copy_cm_negative', False, 1)]
for k,target,invert,expected in jobs:
 a=f'NFT_K{k:03}';env=dict(os.environ,NFT_CORE='1')
 if invert:env['NFT_INVERT']='1'
 with(E/(a+'-controller.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NFT_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 assert r.returncode==expected,(a,'unexpected result, inspect before continuing')
 receipt=json.loads((E/a/'receipt.json').read_text());assert receipt['exit_status']==expected
 text=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED'if expected else 'SUCCESSFUL')in text
 if expected:assert '** 1 of 'in text and 'TIMEOUT'not in text
