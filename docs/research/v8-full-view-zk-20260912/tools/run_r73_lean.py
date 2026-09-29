#!/usr/bin/env python3
"""Focused generated squeeze/inner sampler proofs, cached and resource bounded."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      '9ea038556c6ae2a9ffc89fe93107d947f0cd7b81')
source=source.replace('r68_focused','r73_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
