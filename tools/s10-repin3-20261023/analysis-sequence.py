#!/usr/bin/env python3
"""Sequential capped host regeneration; stop at the first failed stage."""
import subprocess,sys
from pathlib import Path
T=Path(__file__).resolve().parent
for name in ['collect-host','elf-symbol-kinds-host','raw-map-host','prepare-host','elf-host','inspect-frozen-host','ordering-host','cfg-host','instances-host','indirect-host','resolve-host']:
 if len(sys.argv)>1 and name not in ['collect-host','elf-symbol-kinds-host','raw-map-host','prepare-host','elf-host','inspect-frozen-host','ordering-host','cfg-host','instances-host','indirect-host','resolve-host'][['collect-host','elf-symbol-kinds-host','raw-map-host','prepare-host','elf-host','inspect-frozen-host','ordering-host','cfg-host','instances-host','indirect-host','resolve-host'].index(sys.argv[1]):]:continue
 p=subprocess.run([sys.executable,'-B',str(T/'run-host.py'),str(T/(name+'.py')), *(['v3'] if name=='collect-host' else ['v2'] if name=='elf-symbol-kinds-host' else ['v1'] if name=='prepare-host' else [])])
 if p.returncode:raise SystemExit(p.returncode)
