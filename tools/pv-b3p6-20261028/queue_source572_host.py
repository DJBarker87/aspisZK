"""Focused independent targets; stop at the first failure or refusal.
Each wrapper starts at most one admitted, capped scope. No implicit retries.
"""
from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028')
for module in sys.argv[1:]:
 status=subprocess.run(['python3',str(H/'compile_resume18_d569.py'),module],cwd=H).returncode
 if status:raise SystemExit(status)
