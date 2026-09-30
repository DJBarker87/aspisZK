#!/usr/bin/env python3
"""Recheck changed kernels in their composed source, then the whole verifier."""
from pathlib import Path
source=Path(__file__).with_name('run_r106_full.py').read_text()
source=source.replace("'r106_native'","'r115_native'")
old="    compile('r106-terminal-check');run('compact-check.log',[str(cache/'release/r106-terminal-check')])"
new="""    checks=[('r106-terminal-check','compact-check.log'),('r107-semantic-check','semantic-check.log'),
            ('r109-geometry-check','geometry-check.log'),('r112-norm-check','norm-check.log'),
            ('r113-copy-check','copy-check.log')]
    if m['r115_native']['include_tag']:checks.append(('r114-tag-check','tag-check.log'))
    for target,log in checks:
        compile(target);run(log,[str(cache/'release'/target)])"""
assert source.count(old)==1;source=source.replace(old,new)
exec(compile(source,str(Path(__file__).with_name('run_r106_full.py')),'exec'))
