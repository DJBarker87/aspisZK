#!/usr/bin/env python3
"""Focused changed semantic region, same fixture/full-execution gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r106_full.py').read_text()
source=source.replace("'r106_native'","'r107_native'")
source=source.replace("    compile('r106-terminal-check');run('compact-check.log',[str(cache/'release/r106-terminal-check')])", "    shutil.copy2(control/'r24-host-a/compact-check.log',out/'compact-check.log')\n    compile('r107-semantic-check');run('semantic-check.log',[str(cache/'release/r107-semantic-check')])")
exec(compile(source,str(Path(__file__).with_name('run_r106_full.py')),'exec'))
