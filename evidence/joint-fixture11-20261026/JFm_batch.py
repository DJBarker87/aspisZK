from pathlib import Path
import sys,subprocess,json
P=Path(__file__).resolve().parent
n=int(sys.argv[1]);start=int(sys.argv[2]);end=int(sys.argv[3])
for row in range(start,end+1):
 mods=[f'JFm_Q{row:02}Absorb',f'JFm_Q{row:02}Reads',f'JFm_Q{row:02}Source']
 if row==1:mods=mods[1:]
 if row>=15:mods=[f'JFm_Q{row:02}Hashes',f'JFm_Q{row:02}Source']
 for mod in mods:
  assert n<=100
  with (P/f'JFm_{n:03}-driver.log').open('w') as out:r=subprocess.run([sys.executable,str(P/'JFm_compile.py'),str(n),mod],stdout=out,stderr=subprocess.STDOUT)
  print(n,mod,r.returncode,flush=True)
  if r.returncode:sys.exit(r.returncode)
  n+=1
print('NEXT',n,flush=True)
