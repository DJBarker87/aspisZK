import os, sys, subprocess, time, json, signal, hashlib, shutil
from pathlib import Path

root = Path(__file__).resolve().parents[1]
base = Path(__file__).resolve().parent / 'byte-canonicality-check'
base.mkdir(exist_ok=True)
out = base / sys.argv[1]
out.mkdir()
source = root / 'docs/research/100bit-spend-path-20261013/lean/ExtractedRecordByteCanonicality.lean'
objects = base / 'objects'
objects.mkdir(exist_ok=True)
target = objects / 'ExtractedRecordByteCanonicality.olean'
assert source.stem == target.stem == 'ExtractedRecordByteCanonicality'
coordinator = Path('/Users/dominic/ZK/.worktrees/r1-j1-r11-r12-20261015')
header = coordinator / '.j1-record-header-check'
wrapper = coordinator / '.j1-record-source-check/lean-with-cache.py'
backend = Path('/Users/dominic/ZK/external/aeneas/aeneas-verif-workspace/aeneas/backends/lean')
toolchain = Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.31.0')
predecessor = base.parent / 'limb-canonicality-check/objects'
cache = ':'.join(map(str, [objects, predecessor, header / 'objects', backend / '.lake/build/lib/lean']))
cmd = ['/usr/bin/time', '-l', '/Users/dominic/.elan/bin/lake', 'env', 'python3',
       str(wrapper), cache, '-M3500', '-R', str(source.parent), '-o', str(target), str(source)]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins = {str(source): sha(source), str(wrapper): sha(wrapper)}
for path in [source.parent / 'ExtractedRecordLimbCanonicality.lean', predecessor / 'ExtractedRecordLimbCanonicality.olean']:
    pins[str(path)] = sha(path)
expected = {'Types': '2130207194aebca5e06bf9a761c0b797e8d211a36c8f1eaf31a7b25bef71f6cc',
            'Funs': 'f6a3d5b95b781458af5a0118b76d39a14243b77958ef86eb9e5cac50ac45a2b1'}
retained = root / 'docs/research/100bit-spend-path-20261013/evidence/record-parser-local-extraction-20261015/parse-record-f-header-array-20261015/generated/AspisR1RecordParser'
for stem in ['Types', 'Funs']:
    for path in [header / 'AspisR1RecordParser' / (stem + '.lean'),
                 retained / (stem + '.lean')]:
        pins[str(path)] = sha(path)
        assert pins[str(path)] == expected[stem]
    path = header / 'objects/AspisR1RecordParser' / (stem + '.olean')
    pins[str(path)] = sha(path)
runtime = {'version': subprocess.check_output([str(toolchain / 'bin/lean'), '--version'], text=True).strip(),
           'sha256': {str(path): sha(path) for path in
                      [toolchain / 'bin/lean', *sorted((toolchain / 'lib/lean').glob('libleanshared*.dylib'))]}}
assert runtime['version'].startswith('Lean (version 4.31.0,')
shutil.copy2(source, out / source.name)
shutil.copy2(Path(__file__), out / Path(__file__).name)
(out / 'lean-runtime.json').write_text(json.dumps(runtime, indent=2) + '\n')
start = time.monotonic()
peak = 0
killed = False
before = subprocess.check_output(['/usr/sbin/sysctl', 'vm.swapusage'], text=True).strip()
with (out / 'lean.log').open('w') as log:
    p = subprocess.Popen(cmd, cwd=backend, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    while p.poll() is None:
        ps = subprocess.check_output(['/bin/ps', '-axo', 'pid=,pgid=,rss='], text=True)
        rss = sum(int(z[2]) for line in ps.splitlines() if len(z := line.split()) == 3 and int(z[1]) == p.pid)
        peak = max(peak, rss)
        if rss >= 4 * 1024 * 1024:
            killed = True
            os.killpg(p.pid, signal.SIGKILL)
            break
        time.sleep(.05)
    rc = p.wait()
record = {'command': cmd, 'cwd': str(backend), 'source_pins': pins, 'runtime': runtime,
          'checkout_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
          'exit_status': rc, 'wall_seconds': round(time.monotonic() - start, 3),
          'peak_group_rss_kib': peak, 'guard_kib': 4 * 1024 * 1024, 'killed': killed,
          'system_swap_before': before,
          'system_swap_after': subprocess.check_output(['/usr/sbin/sysctl', 'vm.swapusage'], text=True).strip(),
          'scope': 'One Lean4.31 file against exact final-F readonly objects; no cold dependency build. Max RSS, process swaps and axioms in lean.log.'}
(out / 'receipt.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
print((out / 'lean.log').read_text())
sys.exit(rc)
