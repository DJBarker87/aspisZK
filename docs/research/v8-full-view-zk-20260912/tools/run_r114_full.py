#!/usr/bin/env python3
"""Fixed Copy-tag program and complete unchanged-proof gate."""
from pathlib import Path
source=Path(__file__).with_name('run_r107_full.py').read_text()
source=source.replace("'r107_native'","'r114_native'")
source=source.replace('r107-semantic-check','r114-tag-check').replace('semantic-check.log','tag-check.log')
exec(compile(source,str(Path(__file__).with_name('run_r107_full.py')),'exec'))
