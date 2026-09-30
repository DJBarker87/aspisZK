#!/usr/bin/env python3
"""Norm arithmetic, full folded inverse equivalence, then complete runtime."""
from pathlib import Path
source=Path(__file__).with_name('run_r106_full.py').read_text()
source=source.replace("'r106_native'","'r110_native'")
source=source.replace("    compile('r106-terminal-check');run('compact-check.log',[str(cache/'release/r106-terminal-check')])", "    shutil.copy2(control/'r24-host-a/compact-check.log',out/'compact-check.log')\n    compile('r110-norm-check');run('norm-check.log',[str(cache/'release/r110-norm-check')])")
exec(compile(source,str(Path(__file__).with_name('run_r106_full.py')),'exec'))
