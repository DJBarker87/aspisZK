"""Sequential focused dependents; at most one capped Lean scope at any time."""
from run import H
import subprocess,sys
for m in ['PV_B3P_NthSource559227','PV_B3P_NthFormatting559227','PV_B3P_DependencyKernel559227','PV_B3P_Integration559227']:
 r=subprocess.run([sys.executable,str(H/'compile_resume18_extended.py'),m])
 if r.returncode:raise SystemExit(r.returncode)
