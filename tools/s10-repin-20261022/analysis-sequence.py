#!/usr/bin/env python3
"""Sequential capped host regeneration; stop at the first failed stage."""
import subprocess,sys
from pathlib import Path
T=Path(__file__).resolve().parent
for name in ['collect-host','elf-symbol-kinds-host','raw-map-host','prepare-host','elf-host','inspect-frozen-host','ordering-host','cfg-host','instances-host','indirect-host','resolve-host']:
 p=subprocess.run([sys.executable,'-B',str(T/'run-host.py'),str(T/(name+'.py'))])
 if p.returncode:raise SystemExit(p.returncode)
