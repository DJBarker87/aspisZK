#!/usr/bin/env python3
"""Sequential capped sweep of accepted R1 stage-1 + Pool settlement runs.

Run inside one capped scope, e.g.
  systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 \
      -p TasksMax=64 python3 sweep.py plan.json
plan.json: {"driver":..., "pool":..., "verifier":..., "registry":..., "out":...,
            "runs":[{"label":..., "kind":"transfer|withdrawal", "args":[...]}, ...],
            "trace_dir": optional (sets SBF_TRACE_DIR per run)}
Every run records command, exit status, wall time, peak RSS and swaps (from
/usr/bin/time -v) in ledger.jsonl, and the parsed CU result in sweep.jsonl.
Existing labels in ledger.jsonl are skipped (resumable, never rerun).
"""
import json, os, re, subprocess, sys, time
from pathlib import Path

plan = json.loads(Path(sys.argv[1]).read_text())
out = Path(plan['out']); out.mkdir(parents=True, exist_ok=True)
ledger = out / 'ledger.jsonl'; sweep = out / 'sweep.jsonl'
done = set()
if ledger.exists():
    done = {json.loads(l)['label'] for l in ledger.read_text().splitlines() if l.strip()}
cg = '/sys/fs/cgroup' + Path('/proc/self/cgroup').read_text().split('0::', 1)[1].strip()
limits = {n: Path(cg, n).read_text().strip() for n in ['memory.high', 'memory.max', 'memory.swap.max']}
assert limits['memory.swap.max'] == '0' and int(limits['memory.max']) <= 8 * 2**30, limits
os.umask(0o077)

def metric(text, name):
    m = re.search(re.escape(name) + r':\s*(\d+)', text)
    return int(m[1]) if m else None

for run in plan['runs']:
    label = run['label']
    if label in done:
        continue
    rdir = out / 'runs' / label; rdir.mkdir(parents=True, exist_ok=False)
    evidence = rdir / 'evidence.json'; task = rdir / 'task'
    cmd = [plan['driver'], plan['pool'], plan['verifier'], plan['registry'], str(evidence), str(task),
           run['kind'], run.get('scenario', 'success'), *run['args']]
    env = dict(os.environ)
    if plan.get('trace_dir'):
        env['SBF_TRACE_DIR'] = str(Path(plan['trace_dir']) / label)
    start = time.monotonic()
    with open(rdir / 'stdout.log', 'w') as so, open(rdir / 'stderr.log', 'w') as se:
        status = subprocess.run(['/usr/bin/time', '-v', '-o', str(rdir / 'time.log'), *cmd],
                                stdout=so, stderr=se, env=env, cwd=str(rdir), timeout=1800).returncode
    wall = time.monotonic() - start
    tl = (rdir / 'time.log').read_text() if (rdir / 'time.log').exists() else ''
    rec = dict(label=label, kind=run['kind'], args=run['args'], command=cmd, exit_status=status,
               wall_seconds=round(wall, 3), peak_rss_kib=metric(tl, 'Maximum resident set size (kbytes)'),
               swaps=metric(tl, 'Swaps'), cgroup=cg, limits=limits,
               cgroup_memory_peak_bytes=int(Path(cg, 'memory.peak').read_text()) if Path(cg, 'memory.peak').exists() else None)
    row = dict(label=label, kind=run['kind'], exit_status=status)
    if status == 0 and evidence.exists():
        d = json.loads(evidence.read_text()); e = d['execution']
        nested = [int(m[1]) for l in e['logs'] if (m := re.search(r'Program 7Q2\S* consumed (\d+) of', l))]
        row.update(stage1_cu=e['stage1_compute_units'], settlement_cu=e['compute_units'],
                   nested_stage2_cu=nested[0] if len(nested) == 1 else None,
                   stage1_error=e['stage1_error'], error=e['error'], outcome=e['outcome'],
                   pairs=e['populated_pairs_requested'], inputs=e.get('cu_bound_inputs'),
                   history_mode=d['authenticated_path']['history_mode'],
                   output_lane=d['authenticated_path']['selected_output_lane'],
                   mask_mode=d['fixture'].get('mask_mode'), fixture_kind=d['fixture'].get('kind'))
    with ledger.open('a') as f: f.write(json.dumps(rec) + '\n')
    with sweep.open('a') as f: f.write(json.dumps(row) + '\n')
    print(json.dumps(row), flush=True)
