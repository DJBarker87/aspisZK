#!/usr/bin/env python3
"""Source-pinned augmented-root residual test, not a protocol modification."""
from pathlib import Path
from r119_source_program import build
source=Path(__file__).with_name('run_r118_source.py').read_text().replace('r118','r119')
source=source.replace("shutil.copy2(here/name,ex/name);changed.append(ex/name)",
 "(ex/name).write_text(build((here/'r118_source_boundary.rs').read_text()));changed.append(ex/name)")
source=source.replace('only three 13-by-28 eliminations','one 13-by-25 elimination and exact low-map checks')
exec(compile(source,str(Path(__file__).with_name('run_r118_source.py')),'exec'))
