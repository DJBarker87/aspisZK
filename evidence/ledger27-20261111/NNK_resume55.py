from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
for n,kind,mode in [(55,'audit','repair-window48'),(56,'audit','repair-window49'),(57,'audit','window50'),(58,'lean','NNK_FinalStatements'),(59,'audit','scan'),(60,'audit','all-close')]:
 a=f'NNK_L{n:03}';assert not(E/a).exists()
 with(E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NNK_run.py'),a,kind,mode],stdout=f,stderr=subprocess.STDOUT)
 print(a,mode,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
