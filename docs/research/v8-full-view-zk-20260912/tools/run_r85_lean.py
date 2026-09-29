#!/usr/bin/env python3
"""Focused circle-observer leaves, reusing the pinned R80 compiled cache."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text().replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
    '16c672f16becb0e1cbfeec350c01aa25277b24ba').replace('r68_focused','r85_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
