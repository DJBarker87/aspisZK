#!/usr/bin/env python3
"""Focused four-limb reconstruction proofs, pinned cached full runtime."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      '8b8a8e43a498cbf294e9e4f132a9dc5a22ede2fc')
source=source.replace('r68_focused','r77_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
