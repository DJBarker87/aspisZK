#!/usr/bin/env python3
"""Packed private representation: full source and complete runtime gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r88_full.py').read_text()
source=source.replace("and 'r88_alignment' in m", "and 'r89_packed' in m")
source=source.replace("m['r88_alignment']['control']", "m['r89_packed']['control']")
exec(compile(source,str(Path(__file__).with_name('run_r88_full.py')),'exec'))
