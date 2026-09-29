#!/usr/bin/env python3
"""Focused explicit sampler/circle namespace transport on the pinned cache."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      '1eff875d763b8d7b591d12f9e5b5138de4fed250')
source=source.replace('r68_focused','r78_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
