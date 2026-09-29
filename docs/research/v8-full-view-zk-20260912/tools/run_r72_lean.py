#!/usr/bin/env python3
"""Focused generated sampler checks in the retained bounded workspace."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      'bc92dd5675b58ba3076b999429f7cbdfc6675baf')
source=source.replace('r68_focused','r72_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
