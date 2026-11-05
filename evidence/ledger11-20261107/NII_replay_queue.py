from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a in json.loads((E/'NII_VALIDATOR_JOBS.json').read_text()):
 if (E/('NII_REPLAY_'+a+'.json')).exists() and json.loads((E/('NII_REPLAY_'+a+'.json')).read_text())['exit_status']==0:continue
 with (E/('NII_REPLAY_'+a+'.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NII_replay.py'),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
