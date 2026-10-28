from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume'
modules=['JHb_DataMaster','JHg_DataMaster','JHb_DataForest','JHg_DataForest','JHb_DataLane','JHb_DataRegistry','JHb_DataEntry']
for a,m in enumerate(modules,60950):
 r=subprocess.run([sys.executable,str(R/'tools/pv-2tnv-20261028/check.py'),str(a),m,str((E/(m+'.lean.txt')).relative_to(R))])
 if r.returncode:sys.exit(r.returncode)
