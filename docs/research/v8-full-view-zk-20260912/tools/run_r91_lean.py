#!/usr/bin/env python3
"""Focused block/source leaves with the existing source-pinned cache."""
from pathlib import Path
source=Path(__file__).with_name('run_r86_lean.py').read_text().replace(
    'b1a0fdc499fdfa556c4c74cf7e4471bd7a1a15e4','8d84840936fb9338c71b045f527c065b691ba125').replace('r86_focused','r91_focused')
exec(compile(source,str(Path(__file__).with_name('run_r86_lean.py')),'exec'))
