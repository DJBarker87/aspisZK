from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
jobs=[(3,0,'control')]+[(4+2*(m-1)+b,m,kind) for m in range(1,9) for b,kind in enumerate(['cut','control'])]
for n,m,kind in jobs:
 a=f'NLR_K{n:03d}';h=f'r1_semantic::NLR_native::window_{m:02d}_{kind}'
 subprocess.run([sys.executable,str(P/'NLR_kconfig.py'),a,h],check=True)
 r=subprocess.run([sys.executable,str(P/'NLR_run.py'),a])
 # PASS0 or matched propertyFAIL1 are classified from their actual native logs below.
 out=(P/a/'stdout.log').read_text()
 if kind=='cut':assert r.returncode==0,(a,out[-1200:])
 else:assert 'VERIFICATION:- FAILED' in out and 'timed out' not in out and 'assertion' in out.lower(),(a,out[-1200:])
