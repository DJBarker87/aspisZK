#!/usr/bin/env python3
"""Focused sampler observer leaves; keep the pinned cache and resource caps."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      '383ff829927ac5a8cf1fc544674ebb16327803b6')
source=source.replace('r68_focused','r79_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
