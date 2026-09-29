#!/usr/bin/env python3
from pathlib import Path
source=Path(__file__).with_name('run_r23_full.py').read_text()
source=source.replace("+(2 if 'r27_sparse_prepare'in m else 0)","+(2 if 'r27_sparse_prepare'in m else 0)+(13 if 'r58_tag'in m else 0)")
start=source.index("    if 'r27_sparse_prepare'in m:");end=source.index("    run('compile.log'",start)
source=source[:start]+'''    assert 'r58_tag'in m
    run('tag-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin','r58-tag-check'])
    run('tag-check.log',[str(cache/'release/r58-tag-check')])
'''+source[end:]
exec(compile(source,str(Path(__file__).with_name('run_r23_full.py')),'exec'))
