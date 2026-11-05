from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,m in [('NHY_L039','NHY_ZeroLoop'),('NHY_L040','NHY_ZeroStep'),('NHY_L041','NHY_ZeroRun'),('NHY_L042','NHY_AllZeroBridge')]:
 r=subprocess.run([sys.executable,str(E/'NHY_run.py'),a,'lean',m])
 if r.returncode:sys.exit(r.returncode)
