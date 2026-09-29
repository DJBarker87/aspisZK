#!/usr/bin/env python3
"""Arithmetic, affected source, malformed, stack and complete runtime gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r88_full.py').read_text()
source=source.replace("and 'r88_alignment' in m", "and 'r94_products' in m")
source=source.replace("m['r88_alignment']['control']", "m['r94_products']['control']")
source=source.replace("['r69-explicit-check','r81-square-check','r81-basis-check']", "['r94-product-check','r69-explicit-check','r81-square-check','r81-basis-check','r90-gamma-check']")
exec(compile(source,str(Path(__file__).with_name('run_r88_full.py')),'exec'))
