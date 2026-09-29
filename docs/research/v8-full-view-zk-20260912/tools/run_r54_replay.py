#!/usr/bin/env python3
"""Export compiled R54 wrapper-program fixtures in the retained Lean cache."""
from pathlib import Path
source=Path(__file__).with_name('run_r53_replay.py').read_text()
source=source.replace('SamplerReplay','WrapperReplay').replace(
    'a26a468746e9551769ce1d17104050e1fc1bf1fc',
    'eaa0435c1e71b9605af40daf7b07cefd3bcb5e92')
exec(compile(source,str(Path(__file__).with_name('run_r53_replay.py')),'exec'))
