#!/usr/bin/env python3
"""Extract literal weights for the focused two-swap residual certificate."""
from pathlib import Path
from r120_source_program import build
source=Path(__file__).with_name('run_r118_source.py').read_text().replace('r118','r120')
source=source.replace("shutil.copy2(here/name,ex/name);changed.append(ex/name)",
 "(ex/name).write_text(build((here/'r118_source_boundary.rs').read_text()));changed.append(ex/name)")
source=source.replace('only three 13-by-28 eliminations','one 13-by-25 elimination and exact source-weight export')
exec(compile(source,str(Path(__file__).with_name('run_r118_source.py')),'exec'))
