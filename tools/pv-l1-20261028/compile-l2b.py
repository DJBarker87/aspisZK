from pathlib import Path
import sys,subprocess
R=Path(__file__).resolve().parents[2]
mods=['PV_L2B_SamplerLaw','PV_L2B_Cursor','PV_L2B_EntropyTrace','PV_L2B_Guards','PV_L2B_JointTransport']
a=int(sys.argv[1])
for m in mods:
 r=subprocess.run([sys.executable,str(R/'tools/pv-l1-20261028/check.py'),str(a),m],capture_output=True,text=True)
 print(r.stdout[-2500:] if r.returncode else r.stdout[-600:],flush=True)
 if r.returncode:sys.exit(r.returncode)
 a+=1
