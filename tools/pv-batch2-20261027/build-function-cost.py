"""Compile the finite function-cost probe, optimized, without changing shipped code."""
from pathlib import Path
import subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
raise SystemExit(subprocess.run(['cargo','build','--manifest-path',str(H/'function-cost/Cargo.toml'),'--release','--offline','-j','4']).returncode)
