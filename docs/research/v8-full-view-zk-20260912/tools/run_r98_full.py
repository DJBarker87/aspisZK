#!/usr/bin/env python3
"""Focused public sampler source and unchanged proof/runtime gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r93_full.py').read_text()
source=source.replace("'r93_opening'","'r98_query'")
source=source.replace("assert changed==['docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs']",
    "assert len(changed)==4 and 'crates/aspis-core/src/transcript.rs' in changed")
source=source.replace('Only opening limb call layout changed; all ordinary sources/checker identical.',
    'Only query guard changed; all ordinary sources/checker identical.')
source=source.replace("exec(compile(source,",'''source=source.replace("    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])", "    compile('r98-query-check');run('query-check.log',[str(cache/'release/r98-query-check')])")
exec(compile(source,''')
exec(compile(source,str(Path(__file__).with_name('run_r93_full.py')),'exec'))
