#!/usr/bin/env python3
"""Focused query leaves, reusing the pinned R85 compiled workspace."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text().replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
    'b1a0fdc499fdfa556c4c74cf7e4471bd7a1a15e4').replace('r68_focused','r86_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
