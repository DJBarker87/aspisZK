#!/usr/bin/env python3
"""Analyze the resource-receipted repeat of the exact full R115 trace."""
from pathlib import Path
source=Path(__file__).with_name('analyze_r24_full_trace.py').read_text()
source=source.replace('full-trace/','full-trace-cap-b/')
old="p.add_argument('--stage',type=Path,required=True);a=p.parse_args();s=a.stage"
new=old+"""
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
caps={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert caps=={'memory.high':str(2**30),'memory.max':str(2*2**30),'memory.swap.max':'0','pids.max':'128'}
(s/'full-trace-cap-b/analysis-resources.json').write_text(json.dumps(caps,indent=2)+'\\n')
"""
assert source.count(old)==1;source=source.replace(old,new)
exec(compile(source,str(Path(__file__).with_name('analyze_r24_full_trace.py')),'exec'))
