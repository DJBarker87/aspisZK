#!/usr/bin/env python3
"""Sequential capped attempts; never retries failed/stalled targets."""
import json,subprocess,sys
from pathlib import Path
BASE=Path('/home/dombarker/project-offloads/codex-cx-r22-overflow-20261021')
CASES=[('18-parent-group', 'multiproof::parent_group_all_frontiers'), ('19-binary-step', 'multiproof::binary_frontier_step'), ('20-sibling-cursor', 'multiproof::sibling_cursor_step'), ('21-insertion-inner', 'multiproof::insertion_inner_all_positions'), ('22-dedup-step', 'multiproof::dedup_step_all_positions'), ('23-slots', 'layout::all_compact_slots'), ('24-openings', 'layout::all_compact_openings'), ('25-batch-keys', 'layout::batch_key_ranges'), ('26-reader4', 'layout::checkpoint_reader_4'), ('27-reader16', 'layout::checkpoint_reader_16'), ('28-reader32', 'layout::checkpoint_reader_32')]
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
