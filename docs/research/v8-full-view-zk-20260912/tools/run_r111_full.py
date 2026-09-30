#!/usr/bin/env python3
"""Fixed-offset follow-up to the rejected dynamic decoder."""
from pathlib import Path
source=Path(__file__).with_name('run_r108_full.py').read_text()
source=source.replace("'r108_native'","'r111_native'")
source=source.replace('r108-decode-check','r111-decode-check')
exec(compile(source,str(Path(__file__).with_name('run_r108_full.py')),'exec'))
