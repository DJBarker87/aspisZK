#!/usr/bin/env python3
"""Focused canonical marker proof in the retained source-aware workspace."""
from pathlib import Path
source=Path(__file__).with_name('run_r50_lean.py').read_text()
source=source.replace('r50_focused','r55_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a',
    '85f18af7ce9078b751ca1b8fb981f1ce35396499')
exec(compile(source,str(Path(__file__).with_name('run_r50_lean.py')),'exec'))
