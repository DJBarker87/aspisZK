#!/usr/bin/env python3
"""Focused source sampler reads, reusing the pinned full-runtime cache."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      'b963532305dbe50cc0ce68a7c8158104f9353de7')
source=source.replace('r68_focused','r74_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
