"""Serial own queue. Each attempt has its own strict admission and receipt."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(6,'decode_total',True),(7,'field_canonical',False),(8,'field_canonical',True),(9,'field_noncanonical',False),(10,'field_noncanonical',True),(11,'field_short',False),(12,'field_short',True)]
for number,name,control in jobs:
 env=os.environ.copy()
 if control:env['NJU_INVERT']='1'
 p=subprocess.run(['python3',str(E/'NJU_run.py'),f'NJU_K{number:03d}','kani','weights::NJU_finish::'+name],env=env)
 receipt=E/f'NJU_K{number:03d}'/'receipt.json'
 if not receipt.exists():raise SystemExit('Missing receipt; recover read-only')
 r=json.loads(receipt.read_text())
 if p.returncode not in ([1,10] if control else [0]):raise SystemExit('Unexpected result; inspect before changing input')
