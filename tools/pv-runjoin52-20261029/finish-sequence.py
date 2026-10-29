from pathlib import Path
import subprocess,sys,json
T=Path(__file__).parent;R=T.resolve().parents[1];E=R/'evidence/pv-runjoin52-20261029'
mods=['CircleRawSampler52','CircleRawMap52','CircleOwnedSampler52','CircleOwnedMap52','CircleOwnedFallback52','CircleOwnedComplete52','CircleNeutralSelected52','CircleOwnedSelected52','CircleInstalled52','CircleNeutralBase52','CircleNeutralScalar52','CircleNeutralAdd52','CircleOwnedTower52']
a,off=map(int,sys.argv[1:])
for m in mods[off:]:
 assert a<65597
 r=subprocess.run([sys.executable,str(T/'focused.py'),str(a),'R1Z.PV_RunJoin_'+m])
 if r.returncode:sys.exit(r.returncode)
 a+=1
