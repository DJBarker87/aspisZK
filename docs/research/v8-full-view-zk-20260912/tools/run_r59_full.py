#!/usr/bin/env python3
from pathlib import Path
source=Path(__file__).with_name('run_r23_full.py').read_text()
source=source.replace("+(2 if 'r27_sparse_prepare'in m else 0)","+(2 if 'r27_sparse_prepare'in m else 0)+(13 if 'r59_partial_dot'in m else 0)")
start=source.index("    if 'r27_sparse_prepare'in m:");end=source.index("    run('compile.log'",start)
source=source[:start]+'''    assert 'r59_partial_dot'in m
    for name in ['r56-product-check','r24-dot-check']:
        run(name+'-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin',name])
        run(name+'.log',[str(cache/'release'/name)])
'''+source[end:]
exec(compile(source,str(Path(__file__).with_name('run_r23_full.py')),'exec'))
