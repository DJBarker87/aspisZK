#!/usr/bin/env python3
"""Focused R98 entry leaves; no dependency rebuild and no opaque guard model."""
from pathlib import Path
source=Path(__file__).with_name('run_r91_lean.py').read_text().replace(
 '8d84840936fb9338c71b045f527c065b691ba125','da1110c9f49179292d332e1d300f618ba2d8f5d4').replace('r91_focused','r98_focused')
exec(compile(source,str(Path(__file__).with_name('run_r91_lean.py')),'exec'))
