#!/usr/bin/env python3
"""Focused bounded rejection-loop proofs on the pinned full-runtime cache."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      'f832e5033d9fdfc9b6e59c15f5369feac73b4602')
source=source.replace('r68_focused','r75_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
