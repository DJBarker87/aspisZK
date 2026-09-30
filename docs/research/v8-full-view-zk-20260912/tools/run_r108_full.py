#!/usr/bin/env python3
"""Focused changed packed decoder, same complete proof execution gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r106_full.py').read_text()
source=source.replace("'r106_native'","'r108_native'")
source=source.replace("    shutil.copy2(control/'r24-host-a/opening-check.log',out/'opening-check.log')", "    shutil.copy2(control/'r24-host-a/compact-check.log',out/'compact-check.log')")
source=source.replace("    compile('r106-terminal-check');run('compact-check.log',[str(cache/'release/r106-terminal-check')])", "    compile('r108-decode-check');run('opening-check.log',[str(cache/'release/r108-decode-check')])")
exec(compile(source,str(Path(__file__).with_name('run_r106_full.py')),'exec'))
