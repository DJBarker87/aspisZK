#!/usr/bin/env python3
"""Focused query observer leaves, reusing the R98 compiled dependencies."""
from pathlib import Path
source=Path(__file__).with_name('run_r98_lean.py').read_text().replace(
 'da1110c9f49179292d332e1d300f618ba2d8f5d4','059abfb388290177bbb1857745fc48e3ae9e3833').replace('r98_focused','r100_focused')
exec(compile(source,str(Path(__file__).with_name('run_r98_lean.py')),'exec'))
