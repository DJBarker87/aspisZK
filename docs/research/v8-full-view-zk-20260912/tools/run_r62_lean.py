#!/usr/bin/env python3
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r50_lean.py').read_text().replace('r50_focused','r62_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a','23cf1bd882ccce6f330a4cafb6d39e54c748b984')
exec(compile(source,str(here/'run_r50_lean.py'),'exec'))
