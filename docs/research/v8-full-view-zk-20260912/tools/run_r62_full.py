#!/usr/bin/env python3
"""Focused scalar/general differential then unchanged complete executions."""
from pathlib import Path
source=Path(__file__).with_name('run_r23_full.py').read_text()
source=source.replace("+(2 if 'r27_sparse_prepare'in m else 0)","+(2 if 'r27_sparse_prepare'in m else 0)+(15 if ('r62_entry'in m or 'r62_gather'in m) else 0)")
exec(compile(source,str(Path(__file__).with_name('run_r23_full.py')),'exec'))
