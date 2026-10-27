from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
plans=[f'PV_RunJoin_TransferPrefix{n:02}21' for n in range(2,21)]+[f'PV_RunJoin_WithdrawalPrefix{n:02}21' for n in range(1,21)]
for a,m in enumerate(plans,start=int(sys.argv[1])):
 p=subprocess.run([sys.executable,str(R/'tools/pv-runjoin21-20261027/check.py'),str(a),'R1Z/'+m],cwd=R)
 if p.returncode:sys.exit(p.returncode)
print('39 dependent append prefixes accepted',flush=True)
