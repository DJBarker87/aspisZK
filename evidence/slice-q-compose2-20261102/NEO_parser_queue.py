"""Serial native checks; stop before any next run on an unexpected verdict."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(6,'c_parser',0),(7,'c_parser_wrong',1),(8,'q_parser',0),(9,'q_parser_wrong',1),(10,'limbs_parser',0),(11,'limbs_parser_wrong',1),(12,'wide_parser',0),(13,'wide_parser_wrong',1)]
for n,name,expected in jobs:
 a=f'NEO_K{n:03}'
 r=subprocess.run([sys.executable,str(E/'NEO_kani.py'),a,'field::NEO_parsers::'+name])
 p=E/a/'receipt.json';assert p.exists(),'no terminal receipt; stop'
 d=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 assert d['exit_status']==expected and ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log,'unexpected verdict; inspect before continuation'
