"""Sequential one-module-per-attempt queue; never replay unchanged failures."""
import subprocess,sys
start,first,last=map(int,sys.argv[1:])
for offset,i in enumerate(range(first,last+1)):
 r=subprocess.run([sys.executable,'tools/pv-reach-20261027/resume2-check.py',str(start+offset),f'R1Z/PV_RE_DictSuffix{i:03}'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(i,r.returncode,r.stdout[-650:],flush=True)
 if r.returncode:sys.exit(r.returncode)
