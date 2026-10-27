"""Sequential focused attempts; stop at a failure for source inspection."""
import subprocess,sys,pathlib,json
R=pathlib.Path(__file__).resolve().parents[2];A=int(sys.argv[1])
mods=[f'R1Z/PV_RunJoin_ReconstructWithdrawal{j:02}18' for j in reversed(range(21))]
for m in mods:
 r=subprocess.run([sys.executable,str(R/'tools/pv-runjoin18-20261027/check.py'),str(A),m],cwd=R)
 if r.returncode:sys.exit(r.returncode)
 A+=1
