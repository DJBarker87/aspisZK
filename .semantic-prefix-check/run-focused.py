import hashlib, json, os, signal, subprocess, sys, time
from pathlib import Path

here = Path(__file__).resolve().parent
work = here.parent
module, label = sys.argv[1:3]
name = module.removeprefix('R1')
source = work/'docs/research/100bit-spend-path-20261013/lean'/(name+'.lean')
staged = here/(module+'.lean')
staged.write_bytes(source.read_bytes())
(here/(label+'.source.lean')).write_bytes(source.read_bytes())
pins = json.loads((here/'import-source-pins.json').read_text())
assert not pins['unresolved']
assert all(r.get('exact_source_match_to_cache_revision', True) for r in pins['modules'].values())
objects = here/'objects'
objects.mkdir(exist_ok=True)
caches = [objects, Path('/Users/dominic/.cache/aspis/r1-j1-r7-r8-local-check-20261015-7c5ca8699/objects'), Path('/Users/dominic/ZK/.worktrees/r1-j1-r11-r12-20261015/.j1-merge-check/objects')]
cmd = ['/usr/bin/time', '-l', '/Users/dominic/.elan/bin/lake', 'env', 'python3', str(here/'lean-with-cache.py'), ':'.join(map(str, caches)), '-j1', '-M3500', '-R', str(here), '-o', str(objects/(module+'.olean')), str(staged)]
def swap():
    return subprocess.check_output(['sysctl', 'vm.swapusage'], text=True).strip()
swap_before = swap()
start, peak, killed = time.monotonic(), 0, None
log = here/(label+'.log')
with log.open('w') as output:
    process = subprocess.Popen(cmd, cwd='/Users/dominic/ZK/AspisFormal', stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
    while process.poll() is None:
        rows = subprocess.check_output(['ps', '-axo', 'pid=,pgid=,rss='], text=True)
        usage = sum(int(parts[2]) for row in rows.splitlines() if len(parts := row.split()) == 3 and int(parts[1]) == process.pid)
        peak = max(peak, usage)
        if usage > 4*1024*1024:
            killed = 'sampled aggregate RSS exceeded 4 GiB'
        elif time.monotonic()-start > 180:
            killed = '180-second focused-job timeout'
        if killed:
            os.killpg(process.pid, signal.SIGKILL)
            break
        time.sleep(0.1)
    status = process.wait()
receipt = {'module': module, 'source': str(source), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=work, text=True).strip(), 'command': cmd, 'cwd': '/Users/dominic/ZK/AspisFormal', 'exit_status': status, 'wall_seconds': round(time.monotonic()-start, 3), 'sampled_peak_process_group_rss_kib': peak, 'sampled_stop_threshold_kib': 4*1024*1024, 'lean_memory_limit_mib': 3500, 'timeout_seconds': 180, 'killed': killed, 'global_swap_before': swap_before, 'global_swap_after': swap(), 'axioms_log': log.name, 'no_cold_dependency_build': True, 'cache_source_pins': 'import-source-pins.json', 'scope': 'One focused local Lean 4.32 file using previously compiled dependency objects; no host action.'}
if status == 0:
    receipt['object_sha256'] = hashlib.sha256((objects/(module+'.olean')).read_bytes()).hexdigest()
(here/(label+'.json')).write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
print(log.read_text())
sys.exit(status)
