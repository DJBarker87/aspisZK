#!/usr/bin/env python3
"""Cross-coordinate Copy program, complete unchanged source/proof gate."""
from pathlib import Path
source=Path(__file__).with_name('run_r107_full.py').read_text()
source=source.replace("'r107_native'","'r113_native'")
source=source.replace('r107-semantic-check','r113-copy-check').replace('semantic-check.log','copy-check.log')
exec(compile(source,str(Path(__file__).with_name('run_r107_full.py')),'exec'))
