from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);mods=sys.argv[2:]
for idx,mod in enumerate(mods,start):
 a=f'NLJ_L{idx:03}'
 subprocess.run([sys.executable,str(E/'NLJ_config.py'),a,mod],check=True)
 r=subprocess.run([sys.executable,str(E/'NLJ_run.py'),a])
 if r.returncode:sys.exit(r.returncode)
