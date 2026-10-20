#!/usr/bin/env python3
"""One selected immutable target, resource admission, no automatic retries."""
import json,os,subprocess,sys
from pathlib import Path
BASE=Path('/home/dombarker/project-offloads/codex-cx-r22-overflow2-20261021')
attempt,harness=sys.argv[1:3]
used=0
for scope in Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice').glob('*.scope'):
    try: populated=(scope/'cgroup.events').read_text()
    except OSError: continue
    if 'populated 1' in populated:
        n=(scope/'memory.max').read_text().strip()
        if n=='max':raise SystemExit('uncapped populated scope: '+str(scope))
        used+=int(n)
assert used+8*2**30<=55*2**30,('host reservation exceeds safe limit',used)
out=BASE/'receipts'/attempt
assert not out.exists(),'immutable attempt exists'
print(json.dumps(dict(attempt=attempt,harness=harness,other_memory_max_bytes=used)),flush=True)
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(BASE/'capped.py'),str(out),'--','env','PATH='+str(BASE/'solver/bin')+':/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','timeout','--signal=TERM','--kill-after=10s','240s','/home/dombarker/.cargo/bin/cargo-kani','kani','--lib','--exact','--harness',harness,'--no-assertion-reach-checks','--default-unwind','34','--output-format','old','--solver',os.environ.get('KANI_SOLVER','z3'),'-Z','function-contracts','-Z','stubbing','-Z','unstable-options','--cbmc-args','--object-bits',os.environ.get('KANI_OBJECT_BITS','10')]
sys.exit(subprocess.run(cmd,cwd=BASE/'generated').returncode)
