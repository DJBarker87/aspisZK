#!/usr/bin/env python3
"""Focused private final-vector fold and complete verifier gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r107_full.py').read_text()
source=source.replace("'r107_native'","'r117_native'")
source=source.replace('r107-semantic-check','r117-primal-check').replace('semantic-check.log','primal-check.log')
exec(compile(source,str(Path(__file__).with_name('run_r107_full.py')),'exec'))
