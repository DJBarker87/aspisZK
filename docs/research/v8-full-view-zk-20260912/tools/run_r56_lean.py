#!/usr/bin/env python3
from pathlib import Path
source=Path(__file__).with_name('run_r50_lean.py').read_text().replace('r50_focused','r56_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a','ad3e1634e711f1c1aeaf97271c4934eb07697b5c')
exec(compile(source,str(Path(__file__).with_name('run_r50_lean.py')),'exec'))
