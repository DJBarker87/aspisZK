#!/usr/bin/env python3
"""Canonical square, dependent source, malformed input, stack and complete runtime."""
from pathlib import Path
source=Path(__file__).with_name('run_r88_full.py').read_text()
source=source.replace("and 'r88_alignment' in m", "and 'r96_square' in m")
source=source.replace("m['r88_alignment']['control']", "m['r96_square']['control']")
source=source.replace("['r69-explicit-check','r81-square-check','r81-basis-check']", "['r96-square-check','r69-explicit-check','r81-square-check','r81-basis-check','r90-gamma-check']")
exec(compile(source,str(Path(__file__).with_name('run_r88_full.py')),'exec'))
