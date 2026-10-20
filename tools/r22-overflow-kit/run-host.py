#!/usr/bin/env python3
"""Sequential capped attempts; never retries failed/stalled targets."""
import json,subprocess,sys
from pathlib import Path
BASE=Path('/home/dombarker/project-offloads/codex-cx-r22-overflow-20261021')
CASES=[('17-reduce-safety-only','canonical::canonical::reduce_all_u64'),('03-scalar-add','canonical::canonical::scalar_add_canonical'),('04-packed-add','canonical::canonical::packed_add'),('05-packed-sub','canonical::canonical::packed_sub'),('06-halves','canonical::canonical::half_and_half_pow'),('07-u32-product','canonical::canonical::widened_u32_product'),('08-raw-partials','canonical::canonical::raw_partial_ranges'),('09-raw-c0','canonical::canonical::raw_coordinate0'),('10-raw-c1','canonical::canonical::raw_coordinate1'),('11-raw-c2','canonical::canonical::raw_coordinate2'),('12-raw-c3','canonical::canonical::raw_coordinate3'),('13-dot-prefix','canonical::canonical::dot_prefix_step'),('14-node-single','multiproof::node_count_single'),('15-node-pair','multiproof::node_count_pair'),('16-sort-four','multiproof::sort_dedup_four')]
for attempt,harness in CASES:
    if len(sys.argv)>1 and attempt not in sys.argv[1:]:continue
    # Admission includes populated systemd app scopes; reserve <=55 GiB total.
    used=0
    for scope in Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice').glob('*.scope'):
        try: populated=(scope/'cgroup.events').read_text()
        except OSError: continue
        if 'populated 1' in populated:
            n=(scope/'memory.max').read_text().strip()
            if n=='max':raise SystemExit('uncapped populated scope: '+str(scope))
            used+=int(n)
    assert used+8*2**30<=55*2**30,('host reservation exceeds safe limit',used)
    cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(BASE/'harness/capped.py'),str(BASE/'receipts'/attempt),'--','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','timeout','--signal=TERM','--kill-after=10s','180s','/home/dombarker/.cargo/bin/cargo-kani','kani','--lib','--exact','--harness',harness,'--no-assertion-reach-checks','--default-unwind','20','--output-format','old']
    print(json.dumps({'attempt':attempt,'harness':harness,'other_memory_max_bytes':used}),flush=True)
    status=subprocess.run(cmd,cwd=BASE/'generated').returncode
    print(json.dumps({'attempt':attempt,'launcher_exit':status}),flush=True)
