#!/usr/bin/env python3
from pathlib import Path
source=Path(__file__).with_name('run_r50_lean.py').read_text().replace('r50_focused','r57_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a','80aa7d98ebbc708ef54b947bb1810b913ddd21ec')
exec(compile(source,str(Path(__file__).with_name('run_r50_lean.py')),'exec'))
