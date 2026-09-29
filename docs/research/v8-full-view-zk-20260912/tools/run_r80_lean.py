#!/usr/bin/env python3
"""Focused observed rejection-loop proofs in the retained capped cache."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      '8b4d9f417497961530e818419156ae5968c7ef31')
source=source.replace('r68_focused','r80_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
