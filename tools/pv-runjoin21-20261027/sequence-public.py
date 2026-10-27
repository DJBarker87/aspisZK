from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
if sys.argv[1]=='base':
 plans=[(38249,'PublicScalars'),(38250,'PublicExt'),(38251,'PublicSnapshot'),(38252,'PublicRoots'),(38253,'TransferFrontier00'),(38254,'WithdrawalFrontier00')]
elif sys.argv[1]=='frontier':
 names=[f'{kind}Frontier{n:02}' for kind in ['Transfer','Withdrawal'] for n in range(1,20)]
 plans=list(enumerate(names,38255))
else:raise RuntimeError('unknown proof stage')
for a,stem in plans:
 p=subprocess.run([sys.executable,str(R/'tools/pv-runjoin21-20261027/check.py'),str(a),'R1Z/PV_RunJoin_'+stem+'21'],cwd=R)
 if p.returncode:sys.exit(p.returncode)
print('Stage',sys.argv[1],'accepted',flush=True)
