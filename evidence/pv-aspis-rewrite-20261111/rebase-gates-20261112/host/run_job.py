#!/usr/bin/env python3
"""pv-aspis-rewrite2-20261112 host runner (Stream B); copy of the pv-aspis-rewrite-20261111 runner (work directory and unit prefix changed), itself derived from pv-recover-20261111 tools/run_job.py (work directory, unit prefix, TasksMax from PV_TASKSMAX).

usage: run_job.py NAME EXPECTED_WORK TIMEOUT_S CWD -- CMD...

One capped user scope per job, after the Stream B admission steps used by the
existing launchers:
  1. /home/dombarker/streamb-slots/turn.sh with STREAMB_SLOTS=3 (host cap file
     may lower it); it waits by itself while too many Stream B scopes run;
  2. codex-pv-runjoin-20261026/reservation-existing.py (fail-closed cgroup
     reservation, 55 GiB host limit, 8 GiB request); a refusal waits 180 s and
     retries, it is never bypassed;
  3. systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G
     -p MemorySwapMax=0 -p TasksMax=64 (the caps recorded by the ProverRwFull
     extraction receipts extract-caller-005 / aeneas-caller-005).
Writes runs/NAME/{target.json,turn.log,admission-*.json,stdout.log,stderr.log,
time.log,cgroup.json,receipt.json}. Never deletes anything.
"""
import sys, os, json, time, subprocess, hashlib, pathlib, shlex, re, datetime

W = pathlib.Path("/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112")
ADMIT = '/home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py'
TURN = '/home/dombarker/streamb-slots/turn.sh'
CAPS = dict(MemoryHigh=os.environ.get('PV_MEMHIGH', '6G'), MemoryMax=os.environ.get('PV_MEMMAX', '8G'), MemorySwapMax='0', TasksMax=os.environ.get("PV_TASKSMAX", "256"))


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def main():
    name, expected, tmo, cwd = sys.argv[1:5]
    assert sys.argv[5] == '--'
    cmd = sys.argv[6:]
    assert re.fullmatch(r'[A-Za-z0-9_.-]+', name)
    R = W / 'runs' / name
    R.mkdir(parents=True, exist_ok=False)  # never reuse a run directory
    env = dict(os.environ)
    target = dict(name=name, expected_work=expected, timeout_s=int(tmo), cwd=cwd, command=cmd,
                  caps=CAPS, source_revision=env.get('PV_SRC_REV'), source_archive_sha256=env.get('PV_SRC_TAR_SHA256'),
                  env={k: env.get(k) for k in ['PATH', 'RUSTUP_TOOLCHAIN', 'RUSTFLAGS', 'CARGO_TARGET_DIR',
                                               'CARGO_BUILD_JOBS', 'CARGO_PROFILE_DEV_OPT_LEVEL',
                                               'CARGO_NET_OFFLINE', 'PV_SRC_REV']},
                  print_axioms='N/A: Rust/Charon/Aeneas translation; no Lean theorem checked',
                  utc_start=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (R / 'target.json').write_text(json.dumps(target, indent=2) + '\n')
    # 1. Stream B turn
    t0 = time.time()
    subprocess.run(['bash', TURN], env=dict(env, STREAMB_SLOTS='4'), check=True)
    turn_wait = time.time() - t0
    # 2. reservation admission, retry after refusal
    n = 0
    while True:
        n += 1
        out = R / f'admission-{n}.json'
        r = subprocess.run(['python3', ADMIT, str(out), '--requested-bytes', os.environ.get('PV_REQ_BYTES', str(8 << 30))], capture_output=True, text=True)
        (R / f'admission-{n}.log').write_text(r.stdout + r.stderr)
        try:
            ok = json.loads(out.read_text()).get('allowed') is True
        except Exception:
            ok = False
        if r.returncode == 0 and ok:
            break
        time.sleep(180)
        subprocess.run(['bash', TURN], env=dict(env, STREAMB_SLOTS='4'), check=True)
    # 3. capped scope
    scope = ['systemd-run', '--user', '--scope', '--quiet', f'--unit=pvar2-{name}']
    for k, v in CAPS.items():
        scope += ['-p', f'{k}={v}']
    inner = [sys.executable, str(W / 'tools' / 'inner.py'), str(R / 'cgroup.json'), str(R / 'stdout.log'),
             str(R / 'stderr.log'), 'timeout', str(tmo)] + cmd
    full = scope + ['/usr/bin/time', '-v', '-o', str(R / 'time.log')] + inner
    (R / 'scope-command.json').write_text(json.dumps(full, indent=2) + '\n')
    t1 = time.time()
    p = subprocess.run(full, cwd=cwd, env=env)
    wall_outer = time.time() - t1
    tim = (R / 'time.log').read_text() if (R / 'time.log').exists() else ''
    rec = dict(target)
    for key, pat in dict(exit=r'Exit status: (\d+)', peak_rss_kib=r'Maximum resident set size \(kbytes\): (\d+)',
                         swaps=r'Swaps: (\d+)', wall=r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)').items():
        m = re.search(pat, tim)
        rec[key] = m[1] if m else None
    rec['scope_exit'] = p.returncode
    rec['wall_seconds_outer'] = wall_outer
    rec['turn_wait_seconds'] = turn_wait
    rec['admission_attempts'] = n
    try:
        rec['cgroup'] = json.loads((R / 'cgroup.json').read_text())
    except Exception as e:
        rec['cgroup'] = dict(error=str(e))
    rec['rss_measurement'] = 'GNU time maximum resident set size of the wrapper tree; cgroup memory.peak is separate'
    rec['utc_end'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (R / 'receipt.json').write_text(json.dumps(rec, indent=2) + '\n')
    print(json.dumps({k: rec[k] for k in ['name', 'exit', 'scope_exit', 'wall', 'peak_rss_kib', 'swaps']}))


if __name__ == '__main__':
    main()
