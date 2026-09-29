#!/usr/bin/env python3
"""Alignment: actual arithmetic, opening, compact, wire and complete SBF gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r85_full.py').read_text()
source=source.replace("and 'r85_native' in m", "and 'r85_native' in m and 'r88_alignment' in m")
source=source.replace("'profile_control':m['r85_native']['control']", "'profile_control':m['r88_alignment']['control']")
needle="exec(compile(source,str(Path(__file__).with_name('run_r84_full.py')),'exec'))"
assert source.count(needle)==1
source=source.replace(needle,"""source=source.replace(\"    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])\",\"\"\"
    for name in ['r69-explicit-check','r81-square-check','r81-basis-check']:
        compile(name);run(name+'.log',[str(cache/'release'/name)])
    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])\"\"\")
"""+needle)
exec(compile(source,str(Path(__file__).with_name('run_r85_full.py')),'exec'))
