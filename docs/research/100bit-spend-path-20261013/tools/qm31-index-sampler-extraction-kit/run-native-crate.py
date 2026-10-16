#!/usr/bin/env python3
"""One actual-crate sampler-filtered release test; requires a capped host scope."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path(sys.argv[1]).resolve()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
cgroup_line = Path('/proc/self/cgroup').read_text().strip()
assert cgroup_line.startswith('0::')
cgroup = Path('/sys/fs/cgroup') / cgroup_line[3:].lstrip('/')
limits = {name: (cgroup/name).read_text().strip() for name in ['memory.high','memory.max','memory.swap.max']}
assert limits == {'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
manifest = json.loads((root/'production-archive.json').read_text())
assert sha(root/'production.tar') == manifest['archive_sha256']
assert sha(root/'production/Cargo.lock') == manifest['Cargo.lock_sha256']
pins = json.loads((root/'input/source-pins.json').read_text())
for path,digest in pins['source_files'].items():
    assert sha(root/'production'/path) == digest
out = root/'runs/production-native'
out.mkdir(exist_ok=False)
env = dict(os.environ)
for name in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS',
             'RUSTC','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']:
    env.pop(name,None)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN='stable',
           CARGO_BUILD_JOBS='1', CARGO_TARGET_DIR=str(root/'cargo-target'), CARGO_NET_OFFLINE='true')
rustc = subprocess.check_output(['rustc','--version','--verbose'],env=env,text=True)
cargo = subprocess.check_output(['cargo','--version'],env=env,text=True)
assert 'commit-hash: e408947bfd200af42db322daf0fadfe7e26d3bd1' in rustc
assert cargo.startswith('cargo 1.94.1 ')
tool_paths = {name:subprocess.check_output(['rustup','which',name],env=env,text=True).strip()
              for name in ['rustc','cargo']}
preflight = {'rustc':rustc,'cargo':cargo,'tools':{name:{'path':p,'sha256':sha(Path(p))} for name,p in tool_paths.items()},
             'environment':{name:env[name] for name in ['PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','CARGO_NET_OFFLINE']},
             'source_revision':manifest['source_revision'],'archive':manifest,'limits':limits,
             'cache_origin':'private cp -a --reflink=auto copy of aspis-100bit-field-parser-candidate-20261014/cargo-target-v152; no hardlinks',
             'prior_cache_rustc_info':json.loads((root/'cargo-target/.rustc_info.json').read_text())}
(out/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
command=['cargo','test','--release','--locked','--offline','-p','aspis-r1-cost-probe','--lib','sampler::qm31_index_tests']
start=time.monotonic()
with (out/'stdout.log').open('x') as log:
    result=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),'timeout','--signal=KILL','600',*command],
                          cwd=root/'production',env=env,stdout=log,stderr=subprocess.STDOUT)
timing=(out/'time.log').read_text()
def number(label):
    match=re.search(re.escape(label)+r':\s*(\d+)',timing)
    return int(match[1]) if match else None
receipt={'source_revision':manifest['source_revision'],'command':command,'exit_status':result.returncode,
         'wall_seconds':time.monotonic()-start,'peak_rss_kib':number('Maximum resident set size (kbytes)'),
         'swaps':number('Swaps'),'limits':limits,'cgroup':cgroup_line,
         'memory_events':(cgroup/'memory.events').read_text(),
         'cgroup_memory_peak_bytes':int((cgroup/'memory.peak').read_text()),
         'runner_sha256':sha(Path(__file__)),'scope':'actual-crate filtered release tests; no proof generation or CU replay'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
raise SystemExit(result.returncode)
