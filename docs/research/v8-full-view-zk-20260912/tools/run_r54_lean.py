#!/usr/bin/env python3
"""Focused R54 wrappers using the pinned source-aware Lean cache."""
from pathlib import Path
source=Path(__file__).with_name('run_r50_lean.py').read_text()
source=source.replace('r50_focused','r54_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a',
    'eaa0435c1e71b9605af40daf7b07cefd3bcb5e92')
exec(compile(source,str(Path(__file__).with_name('run_r50_lean.py')),'exec'))
