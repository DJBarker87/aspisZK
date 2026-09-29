#!/usr/bin/env python3
"""Reuse the bounded R68 runner and base-cache preflight for R69 leaves.
The R69 extraction/candidate audit is separate; R66 preflight is not that audit.
"""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      '265a251ecfbff6cd971a32eccd72cff552786885')
source=source.replace('r68_focused','r69_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
