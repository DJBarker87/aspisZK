#!/usr/bin/env python3
"""Final complex product and full source fold/norm gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r110_full.py').read_text()
source=source.replace("'r110_native'","'r112_native'")
source=source.replace('r110-norm-check','r112-norm-check')
exec(compile(source,str(Path(__file__).with_name('run_r110_full.py')),'exec'))
