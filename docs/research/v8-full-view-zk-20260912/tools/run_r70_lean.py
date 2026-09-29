#!/usr/bin/env python3
"""Bounded focused generated-product proofs, using the retained full cache."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r68_lean.py').read_text()
source=source.replace('b99b3220a41429afb4cef6bf033c4ff9584ccf32',
                      '851c10072a74fff8523b8817d791153128cf920e')
source=source.replace('r68_focused','r70_focused')
exec(compile(source,str(here/'run_r68_lean.py'),'exec'))
