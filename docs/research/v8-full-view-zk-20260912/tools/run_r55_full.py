#!/usr/bin/env python3
"""Focused decoder gate then retained complete host/SBF/SVM checks."""
from pathlib import Path
source=Path(__file__).with_name('run_r23_full.py').read_text()
source=source.replace("+(2 if 'r27_sparse_prepare'in m else 0)","+(2 if 'r27_sparse_prepare'in m else 0)+(1 if 'r55_opening'in m else 0)")
start=source.index("    if 'r27_sparse_prepare'in m:")
end=source.index("    run('compile.log'",start)
source=source[:start]+'''    assert 'r55_opening'in m
    run('opening-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin','r55-opening-check'])
    run('opening-check.log',[str(cache/'release/r55-opening-check')])
'''+source[end:]
exec(compile(source,str(Path(__file__).with_name('run_r23_full.py')),'exec'))
