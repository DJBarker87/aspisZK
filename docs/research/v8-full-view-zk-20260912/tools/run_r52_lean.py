#!/usr/bin/env python3
"""Focused R52 targets in the retained source-aware cache workflow."""
from pathlib import Path
source=Path(__file__).with_name('run_r50_lean.py').read_text()
source=source.replace('r50_focused','r52_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a',
    '55f6f65530e6b1dbccd9c4ea23d82268974d45f9')
exec(compile(source,str(Path(__file__).with_name('run_r50_lean.py')),'exec'))
