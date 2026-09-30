#!/usr/bin/env python3
"""Focused two-swap source bindings; reuse the frozen R120 cache."""
from pathlib import Path
source=Path(__file__).with_name('run_r119_lean.py').read_text().replace(
 '3a4a95e8a5f6d5ee1369c37ae6485ea2b32bf757','1cf29982431cc456ec7d0b670b6c221366e557b4').replace('r119_focused','r121_focused')
exec(compile(source,str(Path(__file__).with_name('run_r119_lean.py')),'exec'))
