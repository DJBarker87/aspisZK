from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a in ['NGY','NGX','NHE','NHF','NHI','NHH','NHC']:
 with (E/('NHO_REPLAY_'+a+'.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NHO_replay.py'),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:print((E/('NHO_REPLAY_'+a+'.log')).read_text()[-2200:],flush=True)
