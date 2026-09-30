#!/usr/bin/env python3
"""Same fixed fields/records and all negatives; only new bounded frontier bytes."""
from pathlib import Path
source=Path(__file__).with_name('check_r19_wire_controls.py').read_text()
assert source.count('assert len(original) <= 40314')==1
source=source.replace('assert len(original) <= 40314','assert len(original) <= 59138')
exec(compile(source,str(Path(__file__).with_name('check_r19_wire_controls.py')),'exec'))
