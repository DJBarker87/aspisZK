"""Sequential focused dependents; at most one capped Lean scope at any time."""
from run import H
import subprocess,sys
for m in ['PV_B3P_NthFinalGuard559227','PV_B3P_NthSourceFinal559227','PV_B3P_NthFormattingFinal559227','PV_B3P_DependencyFinal559227','PV_B3P_IntegrationFinal559227']:
 r=subprocess.run([sys.executable,str(H/'compile_resume18_extended.py'),m])
 if r.returncode:raise SystemExit(r.returncode)
