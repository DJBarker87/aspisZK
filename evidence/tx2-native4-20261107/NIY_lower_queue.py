from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,m in zip(range(22,32),['NIY_SemanticCut','NIY_AfterZ0x','NIY_AfterZ0y','NIY_AfterZ1x','NIY_AfterZ1y','NIY_AfterClaim','NIY_AfterRhs','NIY_AfterPower','NIY_AllocationCut','NIY_FinalCut']):
 r=subprocess.run([sys.executable,str(E/'NIY_run.py'),f'NIY_L{a:03d}','lean',m])
 if r.returncode:sys.exit(r.returncode)
