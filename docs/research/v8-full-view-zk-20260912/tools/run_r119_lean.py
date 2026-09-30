#!/usr/bin/env python3
"""One small augmented-section leaf, existing R100 cache, no dependency rebuild."""
from pathlib import Path
source=Path(__file__).with_name('run_r100_lean.py').read_text().replace(
 '059abfb388290177bbb1857745fc48e3ae9e3833','3a4a95e8a5f6d5ee1369c37ae6485ea2b32bf757').replace('r100_focused','r119_focused')
exec(compile(source,str(Path(__file__).with_name('run_r100_lean.py')),'exec'))
