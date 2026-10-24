"""Release only a job-owned Docker go barrier after exact live admission."""
from pathlib import Path
import json


def release(cgroup, output, scanner):
    limits = {k:(cgroup/k).read_text().strip() for k in
              ['memory.high','memory.max','memory.swap.max','pids.max']}
    required = {'memory.high':str(6*2**30),'memory.max':str(8*2**30),
                'memory.swap.max':'0','pids.max':'64'}
    # Never create go, even partially, on a failed cap or aggregate check.
    assert limits == required, limits
    (output/'cap-receipt.json').write_text(json.dumps(dict(cgroup=str(cgroup),limits=limits),indent=2)+'\n')
    result = scanner(requested=0)
    (output/'reservation-at-barrier.json').write_text(json.dumps(result,indent=2)+'\n')
    assert result['allowed'], result
    (output/'go').touch(exist_ok=False)
    return limits
