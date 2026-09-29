#!/usr/bin/env python3
"""Reuse exact-proof host, malformed, SBF and runtime gates for the sparse delta."""
from pathlib import Path
source=Path(__file__).with_name('run_r88_full.py').read_text()
source=source.replace("and 'r88_alignment' in m", "and 'r92_sparse' in m")
source=source.replace("m['r88_alignment']['control']", "m['r92_sparse']['control']")
exec(compile(source,str(Path(__file__).with_name('run_r88_full.py')),'exec'))
