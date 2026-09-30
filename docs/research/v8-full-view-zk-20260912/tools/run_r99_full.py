#!/usr/bin/env python3
"""Focused quotient/fold checks and same-proof complete verifier gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r93_full.py').read_text()
source=source.replace("'r93_opening'","'r99_fold'")
source=source.replace("assert changed==['docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs']",
    "assert len(changed)==9 and all(n.startswith('docs/research/v8-no-work-100-20260907/experiments/') for n in changed)")
source=source.replace('Only opening limb call layout changed; all ordinary sources/checker identical.',
    'Only opening fold/inverse path changed; all ordinary sources/checker identical.')
source=source.replace("exec(compile(source,",'''source=source.replace("    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])", "    compile('r99-fold-check');run('fold-check.log',[str(cache/'release/r99-fold-check')])\\n    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])")
exec(compile(source,''')
exec(compile(source,str(Path(__file__).with_name('run_r93_full.py')),'exec'))
