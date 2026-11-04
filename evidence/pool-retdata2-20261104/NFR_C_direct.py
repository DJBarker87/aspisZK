"""Reallocated unlaunched C51-59 probes to integrated production carrier cuts.
The original geometry experiment is preserved unrun in NFR_C_ghost_native.py.
No existing harness was renamed to obtain a different verdict.
"""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
mapping={'direct':'join','direct-byte':'join-byte','direct-error':'join-decoder','direct-field':'join-saved','direct-call':'join-context','direct-pointer':'join-validator','direct-length':'join-lane','direct-frame':'join-encoder','direct-variant':'join-error'}
subprocess.run([sys.executable,str(E/'NFR_C_join_native.py'),mapping[sys.argv[1]]],check=True)
