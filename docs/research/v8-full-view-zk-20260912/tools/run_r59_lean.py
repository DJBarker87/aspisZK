#!/usr/bin/env python3
from pathlib import Path
source=Path(__file__).with_name('run_r50_lean.py').read_text().replace('r50_focused','r59_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a','6af7c8384ccea9dce41e16075cd29f77179bd8a0')
exec(compile(source,str(Path(__file__).with_name('run_r50_lean.py')),'exec'))
