from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
names=['Field','FieldExternal','FunsExternal','StdExtra','ByteFields','ABI','DecodeModels','DotModel','CircleModel','CheckpointModel','QueryModel','PublicModel','MaskModel','TerminalModel','Funs']
for i,n in enumerate(names,4):
 a=f'SDY_L{i:03}';m='SDY_Join_'+n
 r=subprocess.run(['python3',str(E/'SDY_attempt.py'),a,str(E/(m+'.lean')),m])
 if r.returncode or json.loads((E/a/'receipt.json').read_text())['exit_status']:raise SystemExit(a+' failed')
