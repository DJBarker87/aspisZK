from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
mods=[p['target'][:-5]for p in json.loads((E/'NGC_CHECKPOINT_RETARGET.json').read_text())]
for k,target in enumerate(mods,32):
 a=f'NGC_L{k:03}'
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'lean',target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
