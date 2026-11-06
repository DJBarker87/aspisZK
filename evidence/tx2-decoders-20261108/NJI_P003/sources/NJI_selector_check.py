import subprocess,json
from pathlib import Path
for cmd in [['python3','NHR_stage.py','--check','--out','NJI_BATCH_PREFLIGHT'],['python3','NHR_stage.py','--options','--function','nji_tx2_decoders','--out','NJI_BATCH_OPTIONS']]:
 r=subprocess.run(cmd,capture_output=True,text=True)
 assert r.returncode==0,r.stderr
x=json.loads(Path('NJI_BATCH_OPTIONS/NHR_OPTIONS.json').read_text());cmd=x['charon_command'];assert cmd.count('--start-from')==8
print('Frozen validation and additive eight-root option check PASS')
