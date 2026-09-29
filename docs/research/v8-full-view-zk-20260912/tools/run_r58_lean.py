#!/usr/bin/env python3
from pathlib import Path
source=Path(__file__).with_name('run_r50_lean.py').read_text().replace('r50_focused','r58_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a','e6e2015650ba4104da3797e4c375591ba29e92c0')
exec(compile(source,str(Path(__file__).with_name('run_r50_lean.py')),'exec'))
