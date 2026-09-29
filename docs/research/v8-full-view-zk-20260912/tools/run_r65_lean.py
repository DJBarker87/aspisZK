#!/usr/bin/env python3
"""Focused R65 leaves, reusing the checked R64 runtime and cache."""
from pathlib import Path
import json
here = Path(__file__).parent
# Record the kernel-enforced scope, not merely the intended command flags.
cg = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
resources = {n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert resources == {'memory.high':str(5*2**30),'memory.max':str(7*2**30),
                     'memory.swap.max':'0','pids.max':'128'}
resources['cgroup'] = str(cg)
source = (here / 'run_r64_lean.py').read_text()
source = source.replace("base='a40fb23673ab80c67e99c06bf156f338b12b2a2e'",
                        "base='70b2494f91a4dae94059f96900232dac5a611ccc'")
source = source.replace('r64_focused', 'r65_focused')
source = source.replace('from audit_r64_source import check_current',
                        'from audit_r65_source import check_current')
source = source.replace("root/'aspis-r64-extracted-20260929-b'",
                        "root/'aspis-r65-extracted-20260929-a'")
source = source.replace("sources/'AspisV8R19/GuardedFieldSlice.lean'",
                        "sources/'AspisV8R19/ComplexFieldSlice.lean'")
source = source.replace("Path(__file__).parent/'r64-field-extraction'",
                        "Path(__file__).parent/'r65-field-extraction'")
source = source.replace("exec(compile(source,str(here/'run_r63_lean.py'),'exec'))",
    "source=source.replace(\"records=json.loads((reuse/'metadata.json').read_text())\", "
    "\"records=[r for r in json.loads((reuse/'metadata.json').read_text()) if r['exit']==0]\")\n"
    "source=source.replace(\"assert not a.output.exists();a.output.mkdir()\", "
    "\"assert not a.output.exists();a.output.mkdir();(a.output/'resources.json').write_text(json.dumps(resources,indent=2)+'\\\\n')\")\n"
    "exec(compile(source,str(here/'run_r63_lean.py'),'exec'))")
exec(compile(source, str(here / 'run_r64_lean.py'), 'exec'))
