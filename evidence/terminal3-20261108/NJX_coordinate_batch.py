from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
order=[1,0,2,3,4,5,7,8,9,10,11,12,13]
for n,j in enumerate(order,18):
 subprocess.run([sys.executable,str(E/'NJX_make_lean.py'),str(n),f'NJX_PatternMeaning{j:02}'],check=True)
 r=subprocess.run([sys.executable,str(E/'NJX_run.py'),f'NJX_L{n:03}'])
 if r.returncode:print(f'coordinate {j}: inspect failed attempt NJX_L{n:03}',flush=True)
