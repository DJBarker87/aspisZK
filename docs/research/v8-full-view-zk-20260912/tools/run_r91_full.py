#!/usr/bin/env python3
"""Wide add/sub: affected arithmetic, source, malformed and complete CU gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r88_full.py').read_text()
source=source.replace("and 'r88_alignment' in m", "and 'r91_wide' in m")
source=source.replace("m['r88_alignment']['control']", "m['r91_wide']['control']")
source=source.replace("['r69-explicit-check','r81-square-check','r81-basis-check']", "['r91-add-check','r69-explicit-check','r81-square-check','r81-basis-check','r90-gamma-check']")
exec(compile(source,str(Path(__file__).with_name('run_r88_full.py')),'exec'))
