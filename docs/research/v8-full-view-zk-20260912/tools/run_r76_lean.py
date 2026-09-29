#!/usr/bin/env python3
"""Focused decoder and sampler-model bridges with pinned cached dependencies."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      'dd09920adb9dc1c49364345c1cff9f8c4d2e1424')
source=source.replace('r68_focused','r76_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
