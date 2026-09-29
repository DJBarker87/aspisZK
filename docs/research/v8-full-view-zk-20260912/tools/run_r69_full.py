#!/usr/bin/env python3
"""Focused fixed-arity product check, full source controls and unchanged SVM."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r23_full.py').read_text()
source=source.replace("+(2 if 'r27_sparse_prepare'in m else 0)",
    "+(2 if 'r27_sparse_prepare'in m else 0)+(15 if 'r62_gather'in m else 0)+(5 if 'r69_explicit_product'in m else 0)")
marker="    if 'r27_sparse_prepare'in m:"
assert source.count(marker)==1
source=source.replace(marker,"""    assert 'r69_explicit_product' in m
    run('product-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin','r69-explicit-check'])
    run('product-check.log',[str(cache/'release/r69-explicit-check')])
"""+marker)
exec(compile(source,str(here/'run_r23_full.py'),'exec'))
