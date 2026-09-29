#!/usr/bin/env python3
"""Add the previously unpinned SBF Cargo manifest for profile-only experiments."""
from pathlib import Path
source=Path(__file__).with_name('run_r81_full.py').read_text()
old="+(5 if 'r81_native'in m else 0)"
assert source.count(old)==1
source=source.replace(old,old+"+(1 if 'docs/research/v8-no-work-100-20260907/experiments/performance-sbf/Cargo.toml' in m['files'] else 0)")
needle="    assert 'r81_native' in m"
extra='''    if m.get('r83_native',{}).get('variant') in ['packed','packed-block']:
        run('opening-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin','r55-opening-check'])
        run('opening-check.log',[str(cache/'release/r55-opening-check')])
'''
assert source.count(needle)==1;source=source.replace(needle,needle+'\n'+extra)
try:
    exec(compile(source,str(Path(__file__).with_name('run_r81_full.py')),'exec'))
finally:
    if 'out' in globals() and out.exists() and 'resources' in globals():
        (out/'resources.json').write_text(json.dumps(resources,indent=2)+'\n')
