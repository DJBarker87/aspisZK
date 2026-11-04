"""Serial independent native gates; stop on every unexpected outcome."""
from pathlib import Path
import os,subprocess,json,hashlib
E=Path(__file__).resolve().parent
jobs=[(98, 'field::wide_exact::NFT_wide_square::square_log', False, 0), (99, 'field::wide_exact::NFT_wide_square::square_log', True, 1)]
frozen={}
for name in ['NFT_NATIVE_INPUTS.json','NFT_SOURCE_PINS.json']:
 raw=(E/name).read_bytes();path=E/'NFT_queued_inputs'/(hashlib.sha256(raw).hexdigest()+'.json');path.parent.mkdir(exist_ok=True)
 if not path.exists():path.write_bytes(raw)
 assert path.read_bytes()==raw
 frozen[name]=str(path)
for k,target,invert,expected in jobs:
 a=f'NFT_K{k:03}';env=dict(os.environ);env['NFT_CORE'if not target.startswith('r1_pool_adapter::')else 'NFT_PROGRAM']='1'
 env['NFT_INPUT_SET']=frozen['NFT_NATIVE_INPUTS.json'];env['NFT_PIN_SET']=frozen['NFT_SOURCE_PINS.json']
 if invert:env['NFT_INVERT']='1'
 with(E/(a+'-controller.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NFT_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 assert r.returncode==expected,(a,'unexpected result, inspect before continuing')
 receipt=json.loads((E/a/'receipt.json').read_text());assert receipt['exit_status']==expected
 text=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED'if expected else 'SUCCESSFUL')in text
 if expected:
  if k==68:
   assert '** 2 of 'in text and 'indices[at] == if cfg!(NFT_invert)'in text and 'assertion failed: !cfg!(NFT_invert)'in text
  else:assert '** 1 of 'in text
  assert 'TIMEOUT'not in text and 'CBMC timed out'not in text
