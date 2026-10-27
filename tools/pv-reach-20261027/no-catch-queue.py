import subprocess,sys,time,pathlib,json
start,first,last=map(int,sys.argv[1:])
for offset,i in enumerate(range(first,last+1)):
 a=start+offset
 r=subprocess.run([sys.executable,'tools/pv-reach-20261027/resume3-check.py',str(a),f'R1Z/PV_RE_NoCatchChunk{i:03}'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(i,r.returncode,r.stdout[-850:],flush=True)
 if r.returncode:sys.exit(r.returncode)
