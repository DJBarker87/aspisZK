#!/usr/bin/env python3
"""Focused inverse targets with the current split reducer dependencies."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r50_lean.py').read_text().replace('r50_focused','r60_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a','eb51ef6ea5be51585ee40da75a86567b92c1575e')
exec(compile(source,str(here/'run_r50_lean.py'),'exec'))
