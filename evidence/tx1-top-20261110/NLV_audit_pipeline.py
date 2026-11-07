from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent

def command(args,stop=True):
 p=subprocess.run([sys.executable,*map(str,args)])
 if stop and p.returncode:raise SystemExit(p.returncode)
 return p.returncode

def run(a):
 with(E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NLV_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,'exit',r.returncode,flush=True);return r.returncode

command([E/'NLV_batch.py','99','NLV_BatchInstall'])
command([E/'NLV_prepare_audit.py'])
command([E/'NLV_batch.py','100','NLV_COMBINED_IMPORT'])
for n,mode in [(101,'Driver'),(102,'ProofDriver'),(103,'link')]:
 a=f'NLV_L{n:03d}';command([E/'NLV_audit_build.py',a,mode])
 if run(a):raise SystemExit(1)
for n,mode in [(104,'fixtures'),(105,'scan')]+[(106+j,'proof'+str(j))for j in range(30)]+[(136,'close')]:
 a=f'NLV_L{n:03d}';command([E/'NLV_audit_config.py',a,mode]);rc=run(a)
 if rc and not mode.startswith('proof'):raise SystemExit(1)
 if rc:
  p=E/'NLV_audit'/mode/(mode+'.json')
  if not p.exists():raise SystemExit('Raw scope incomplete: isolate before continuing')
  # Retain disagreements/failures verbatim; independent groups continue.
  print(mode,'nonzero retained; inspect raw verdict',flush=True)
