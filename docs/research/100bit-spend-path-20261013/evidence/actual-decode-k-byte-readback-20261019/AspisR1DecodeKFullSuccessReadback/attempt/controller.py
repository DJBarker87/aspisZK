import datetime, hashlib, json, pathlib, subprocess, time
from zoneinfo import ZoneInfo

G = 1024 ** 3
HOST_MIN = 62 * G
FINITE_LIMIT = 48 * G
UNBOUNDED_LIMIT = 8 * G
CAP = 7 * G // 2
UNIT = 'aspis-decodek-full-success-readback-v5-20261018'
ATT = pathlib.Path('/tmp/decodek-full-success-readback-v5-attempt-20261018')
SRC = pathlib.Path('/tmp/DecodeKFullSuccessReadback-v5.lean')
SRC_SHA = '0c8fc2a488cced62273578c491e8ff2b701a33288b60415d03ba9266b2dda617'
OBJROOT = pathlib.Path('/tmp/decode-k-full-v10-coherent-objects-v1')
OBJ = OBJROOT / 'AspisR1DecodeKFullSuccessReadback.olean'
INVROOT = pathlib.Path('/tmp/decode-k-canonical-array-invariant-v1-objects')
INV = INVROOT / 'AspisR1DecodeKCanonicalArrayInvariant.olean'
INV_SHA = '6b986370b4db95c5a5370cfee20403465171c45212ce343f8e67cc02422cc65f'
M31 = pathlib.Path('/tmp/decode-k-full-v10-m31-objects-v2')
V10 = pathlib.Path('/tmp/decode-k-full-v10-lean-objects-v2')
CMQ = pathlib.Path('/tmp/decode-k-full-v10-cmq-v6-objects')
HELPER_SHA = '4a121d7ff4c8bcca6b5f0ef88b1995c2fd80e03ce1f75ddfb7023bb5181667ce'
COLLECTOR = pathlib.Path('/tmp/collect-nuc-cgroups-review.py')
COLLECTOR_SHA = '4fc152ea4f88742fb460c301ae17446f1d1ba9162acdaafb37d80e60c4907800'
LEAN = pathlib.Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
ENVIRONMENT = pathlib.Path('/tmp/serializer-bridge-focused-workspace-20261018/environment.json')

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def need(ok, msg):
    if not ok: raise SystemExit('preflight refused: ' + msg)

def inventory():
    data = json.loads(subprocess.run(['python3', str(COLLECTOR)], check=True,
                                     capture_output=True, text=True).stdout)
    finite_sum = int(data['effective_sum_bytes'])
    finite_paths = [pathlib.Path(r['path']) for r in data['effective_reservation_nodes']]
    unbounded = [r for r in data['all_populated_cgroups'] if r['scope'] and r['max'] == 'max']
    outer = []
    for row in unbounded:
        path = pathlib.Path(row['path'])
        if any(parent == path or parent in path.parents for parent in finite_paths): continue
        if any(path in pathlib.Path(other['path']).parents for other in unbounded if other is not row): continue
        outer.append(row)
    return {
        'timestamp_utc': data['timestamp_utc'],
        'MemTotal_bytes': int(data['MemTotal_kB']) * 1024,
        'MemAvailable_bytes': int(data['MemAvailable_kB']) * 1024,
        'effective_finite_sum_bytes': finite_sum,
        'candidate_job_cap_bytes': CAP,
        'finite_plus_job_bytes': finite_sum + CAP,
        'uncapped_outermost_current_bytes': sum(int(r['current_bytes'] or 0) for r in outer),
        'uncapped_outermost_scopes': outer,
        'all_populated_cgroups': data['all_populated_cgroups'],
        'effective_reservation_nodes': data['effective_reservation_nodes'],
        'collector_source_sha256': COLLECTOR_SHA,
    }

def check_gate(snap, launch):
    need(snap['MemTotal_bytes'] >= HOST_MIN, 'MemTotal below 62 GiB')
    need(snap['finite_plus_job_bytes'] <= FINITE_LIMIT, 'finite caps + job exceed 48 GiB')
    need(snap['uncapped_outermost_current_bytes'] <= UNBOUNDED_LIMIT, 'uncapped RSS exceeds 8 GiB')
    avail = 14 * G if launch else 6 * G
    need(snap['MemAvailable_bytes'] >= avail, f'MemAvailable below {avail // G} GiB')
    return snap

def own_cgroup():
    for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
        if p.parent.name == UNIT + '.scope': return p.parent
    return None

def main():
    now = datetime.datetime.now(ZoneInfo('Europe/London'))
    minute = now.hour * 60 + now.minute
    need(minute >= 22 * 60 + 30 or minute < 6 * 60, 'overnight authorization window is closed')
    need(not ATT.exists(), 'attempt directory already exists')
    need(sha(SRC) == SRC_SHA, 'source hash mismatch')
    need(sha(COLLECTOR) == COLLECTOR_SHA, 'cgroup collector hash mismatch')
    need(sha(INV) == INV_SHA, 'canonical invariant object mismatch')
    need(sha(M31 / 'AspisR1DecodeKFullV10ParserCanonicality.olean') ==
         'b2ba6ba5283e890fb789738cac7e141d133daa2623508df97f39a2b6a075eaa6', 'V10 M31 object mismatch')
    need(sha(V10 / 'AspisR1DecodeKFullV10/Funs.olean') ==
         '8e8696389e79756a7bc2a9415974e251d477ffb0b55670bf14db897249b314db', 'V10 Funs object mismatch')
    need(sha(CMQ / 'AspisR1DecodeKFullParserCanonicalityCMQ.olean') ==
         'daafb1a74946ee7a2fd3d56cf21fc2856ba25e0e8bf4aab7ebc47a69c331d723', 'V10 CMQ object mismatch')
    need(sha(OBJROOT / 'AspisR1DecodeKFullHelperCanonicality.olean') == HELPER_SHA,
         'helper canonicality object mismatch')
    need(sha(OBJROOT / 'AspisR1DecodeKFullLoopBodyValueFrame.olean') ==
         'c7492f739aa7984fe075223264539a9b6eed6b4f832b1636f60b87c861426c06', 'body value frame object mismatch')
    need(sha(OBJROOT / 'AspisR1DecodeKFullLoopReadback.olean') ==
         'c82b045fc9eea635aeb568d55d3abbd95a4ab4127452611e31856684ebdec36f', 'loop readback object mismatch')
    need(sha(OBJROOT / 'AspisR1DecodeKFullLoopPendingFuel.olean') ==
         '192f107c903e39716ad0d616fb86f40a9e572b1cce5ea2fbcc343a3b13425543', 'pending fuel object mismatch')
    manifest = json.loads((OBJROOT / 'manifest.json').read_text())
    need(len(manifest) == 6, 'coherent V10 manifest entry count mismatch')
    for row in manifest:
        need(sha(OBJROOT / row['module_path']) == row['sha256'],
             'coherent V10 object hash mismatch: ' + row['module_path'])
    need(not OBJ.exists(), 'stable output module already exists')
    env = json.loads(ENVIRONMENT.read_text())
    lp = str(INVROOT) + ':' + str(OBJROOT) + ':' + env['LEAN_PATH']
    pre = check_gate(inventory(), launch=True)
    ATT.mkdir(mode=0o700)
    cmd = ['/usr/bin/env', 'LEAN_PATH=' + lp, str(LEAN), '-M', '3200',
           '-R', '/tmp', '-o', str(OBJ), str(SRC)]
    doc = {
        'target': 'actual V10 decode_k success exposes per-index parser readback',
        'source': str(SRC), 'source_sha256': sha(SRC),
        'output_module': 'AspisR1DecodeKFullSuccessReadback',
        'output_object': str(OBJ), 'Lean': str(LEAN),
        'Lean_commit': '8c9756b28d64dab099da31a4c09229a9e6a2ef35',
        'LEAN_PATH': lp,
        'imports': {'loop_readback': 'c82b045fc9eea635aeb568d55d3abbd95a4ab4127452611e31856684ebdec36f',
                    'pending_fuel': '192f107c903e39716ad0d616fb86f40a9e572b1cce5ea2fbcc343a3b13425543',
                    'canonical_array_invariant': INV_SHA, 'decode_k_helper_canonicality': HELPER_SHA,
                    'body_value_frame': 'c7492f739aa7984fe075223264539a9b6eed6b4f832b1636f60b87c861426c06',
                    'V10_M31': 'b2ba6ba5283e890fb789738cac7e141d133daa2623508df97f39a2b6a075eaa6',
                    'V10_CMQ': 'daafb1a74946ee7a2fd3d56cf21fc2856ba25e0e8bf4aab7ebc47a69c331d723'},
        'resource_policy': {
            'window': '22:30-06:00 Europe/London',
            'finite_plus_job_limit_bytes': FINITE_LIMIT,
            'uncapped_outermost_current_limit_bytes': UNBOUNDED_LIMIT,
            'MemAvailable_launch_min_bytes': 14 * G,
            'MemAvailable_abort_min_bytes': 6 * G,
            'MemoryHigh': '3G', 'MemoryMax': '3584M', 'MemorySwapMax': '0',
            'Lean_memory_limit_MiB': 3200, 'TasksMax': 128,
            'admission_inventory': pre,
        },
    }
    (ATT / 'preflight.json').write_text(json.dumps(doc, indent=2) + '\n')
    timed = ['/usr/bin/time', '-v', '-o', str(ATT / 'time.log')] + cmd
    shell = ' '.join(subprocess.list2cmdline([x]) for x in timed) + ' > ' + str(ATT / 'lean.log') + ' 2>&1'
    wrapped = ['systemd-run', '--user', '--scope', '--quiet', '--unit=' + UNIT,
               '-p', 'MemoryHigh=3G', '-p', 'MemoryMax=3584M', '-p', 'MemorySwapMax=0',
               '-p', 'TasksMax=128', '/bin/bash', '-lc', shell]
    (ATT / 'command.json').write_text(json.dumps({'argv': wrapped, 'lean_argv': cmd}, indent=2) + '\n')
    start = time.monotonic(); proc = subprocess.Popen(wrapped)
    peak = swap_peak = 0; last_gate = 0.0; abort = None
    with (ATT / 'watcher.jsonl').open('x') as log:
        while proc.poll() is None:
            try:
                cg = own_cgroup(); cur = cp = sw = None
                if cg:
                    cur = int((cg / 'memory.current').read_text())
                    cp = int((cg / 'memory.peak').read_text())
                    sw = int((cg / 'memory.swap.current').read_text())
                    peak = max(peak, cp); swap_peak = max(swap_peak, sw)
                row = {'elapsed_s': round(time.monotonic() - start, 3),
                       'own_memory_current': cur, 'own_memory_peak': cp, 'own_swap_current': sw}
                if time.monotonic() - last_gate >= .5:
                    row['inventory'] = check_gate(inventory(), launch=False)
                    last_gate = time.monotonic()
                log.write(json.dumps(row) + '\n'); log.flush()
            except BaseException as e:
                abort = 'watcher_gate_or_error:' + repr(e)
                subprocess.run(['systemctl', '--user', 'kill', '--kill-who=all', UNIT + '.scope'], check=False)
                break
            time.sleep(.05)
        status = proc.wait()
        cg = own_cgroup()
        if cg:
            peak = max(peak, int((cg / 'memory.peak').read_text()))
            swap_peak = max(swap_peak, int((cg / 'memory.swap.current').read_text()))
    receipt = {'target': doc['target'], 'source_sha256': doc['source_sha256'],
               'exit_status': status, 'wall_seconds': round(time.monotonic() - start, 3),
               'watchdog_abort': abort, 'object_sha256': sha(OBJ) if OBJ.exists() else None,
               'cgroup_memory_peak_bytes_sampled': peak, 'cgroup_swap_peak_bytes_sampled': swap_peak,
               'attempt': str(ATT), 'admission_inventory': pre,
               'controller_sha256': sha(pathlib.Path(__file__))}
    (ATT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(status)

if __name__ == '__main__': main()
