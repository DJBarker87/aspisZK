from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
# New domain: roots/recordmetadata now use original13831 allocation. Payload
# remains one32-byte window and additionally asserts pre-call snapshot frame.
jobs=[(20+2*j+b,m,k)for j,m in enumerate([1,2,4,5,7,8,0,3,6])for b,k in enumerate(['cut','control'])]
for n,m,kind in jobs:
 a=f'NLR_K{n:03d}';h=f'r1_semantic::NLR_native::window_{m:02d}_{kind}'
 subprocess.run([sys.executable,str(P/'NLR_kconfig.py'),a,h],check=True)
 r=subprocess.run([sys.executable,str(P/'NLR_run.py'),a])
 out=(P/a/'stdout.log').read_text()
 if kind=='cut':assert r.returncode==0,(a,out[-1200:])
 else:assert 'VERIFICATION:- FAILED' in out and 'timed out' not in out and 'assertion' in out.lower(),(a,out[-1200:])
