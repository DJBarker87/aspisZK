from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);modules=sys.argv[2:]
for n,m in enumerate(modules,start):
 a=f'NLV_L{n:03d}'
 subprocess.run([sys.executable,str(E/'NLV_config.py'),a,m],check=True)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NLV_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,m,'exit',r.returncode,flush=True)
 if r.returncode:break
