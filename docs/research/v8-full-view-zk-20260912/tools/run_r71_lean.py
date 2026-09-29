#!/usr/bin/env python3
"""Focused circle execution proofs; pinned cache and enforced no-swap scope."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      'bf9e352530094780724cb34648a80526befe6767')
source=source.replace('r68_focused','r71_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
