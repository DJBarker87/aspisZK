import pathlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[2];a=int(sys.argv[1])
for r in [1,2,3,*range(5,18),19,20,21]:
 p=subprocess.run([sys.executable,str(R/'tools/pv-runjoin19-20261027/check.py'),str(a),f'R1Z/PV_RunJoin_IndexedRound{r:02}19'],cwd=R)
 if p.returncode:sys.exit(p.returncode)
 a+=1
