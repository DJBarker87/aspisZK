#!/usr/bin/env python3
"""Focused R53 sampler leaves, reusing the pinned source-aware cache."""
from pathlib import Path
source=Path(__file__).with_name('run_r50_lean.py').read_text()
source=source.replace('r50_focused','r53_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a',
    'a26a468746e9551769ce1d17104050e1fc1bf1fc')
exec(compile(source,str(Path(__file__).with_name('run_r50_lean.py')),'exec'))
