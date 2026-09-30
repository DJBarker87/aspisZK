#!/usr/bin/env python3
"""Recover missing in-scope cap evidence without overwriting the original trace."""
from pathlib import Path
source=Path(__file__).with_name('run_r85_trace.py').read_text()
old="    out=s/'full-trace';assert not out.exists();out.mkdir()"
new="""    cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
    caps={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
    assert caps=={'memory.high':str(2*2**30),'memory.max':str(3*2**30),'memory.swap.max':'0','pids.max':'128'}
    out=s/'full-trace-cap-b';assert not out.exists();out.mkdir()
    (out/'resources.json').write_text(json.dumps(caps,indent=2)+'\\n')"""
assert source.count(old)==1;source=source.replace(old,new)
exec(compile(source,str(Path(__file__).with_name('run_r85_trace.py')),'exec'))
