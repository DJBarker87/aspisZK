from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in enumerate(sys.argv[2:],int(sys.argv[1])):
 r=subprocess.run([sys.executable,str(E/'LIBC_run.py'),f'LIBC_L{n:03d}','audit',mode])
 if r.returncode:sys.exit(r.returncode)
 subprocess.run(['git','add',str(E)],check=True)
 subprocess.run(['git','commit','-q','-m','Audit LIBC roots '+mode],check=True)
 print(mode+' audit committed',flush=True)
