#!/usr/bin/env python3
"""Focused complete geometry comparison and unchanged-proof SBF gate."""
from pathlib import Path
source=Path(__file__).with_name('run_r106_full.py').read_text()
source=source.replace("'r106_native'","'r109_native'")
source=source.replace('r106-terminal-check','r109-geometry-check')
exec(compile(source,str(Path(__file__).with_name('run_r106_full.py')),'exec'))
