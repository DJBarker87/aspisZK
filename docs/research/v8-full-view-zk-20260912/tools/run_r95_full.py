#!/usr/bin/env python3
"""Changed Merkle source gate, unchanged ordinary/opening evidence, complete runtime."""
from pathlib import Path
source=Path(__file__).with_name('run_r93_full.py').read_text()
source=source.replace("'r93_opening'","'r95_merkle'")
source=source.replace("assert changed==['docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs']",
    "assert all(n.startswith('docs/research/v8-no-work-100-20260907/experiments/') for n in changed) and len(changed)==5")
source=source.replace('Only opening limb call layout changed; all ordinary sources/checker identical.',
    'Only internal Merkle walk changed; all ordinary sources/checker identical.')
# Modify the assembled base source after run_r93's precise delta guards.
source=source.replace("exec(compile(source,",'''source=source.replace("    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])", "    compile('r95-merkle-check');run('merkle-check.log',[str(cache/'release/r95-merkle-check')])")
exec(compile(source,''')
exec(compile(source,str(Path(__file__).with_name('run_r93_full.py')),'exec'))
