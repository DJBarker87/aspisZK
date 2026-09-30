#!/usr/bin/env python3
"""Focused native query test and full unchanged-proof execution gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r107_full.py').read_text()
source=source.replace("'r107_native'","'r116_native'")
source=source.replace('r107-semantic-check','r116-query-check').replace('semantic-check.log','query-check.log')
exec(compile(source,str(Path(__file__).with_name('run_r107_full.py')),'exec'))
