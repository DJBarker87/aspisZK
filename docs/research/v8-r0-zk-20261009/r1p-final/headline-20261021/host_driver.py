"""Run on the build host; one new module, existing env J objects only."""
import hashlib, json, pathlib, re, subprocess, sys
attempt = 9500
module = 'R1Z/PrivacyR1Headline'
revision = sys.argv[1]
j = pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
h = pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019')
t = pathlib.Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
private = pathlib.Path('/home/dombarker/project-offloads/codex-cx-priv-headline-20261021')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = j / 'sources' / (module + '.lean')
envp = h / 'env/J.json'
env = json.loads(envp.read_text())
paths = [j / 'objects'] + [pathlib.Path(p) for p in env['LEAN_PATH'].split(':')]
deps = []
for line in src.read_text().splitlines():
    if not line.startswith('import '): continue
    name = line.split()[1]
    obj = next(p / (name.replace('.', '/') + '.olean') for p in paths if (p / (name.replace('.', '/') + '.olean')).exists())
    dep_src = j / 'sources' / (name.replace('.', '/') + '.lean')
    deps.append(dict(module=name, object_path=str(obj), object_sha256=sha(obj), object_size=obj.stat().st_size,
                     source_sha256=sha(dep_src)))
fp = hashlib.sha256(json.dumps(dict(deps=deps, environment_sha256=sha(envp)),sort_keys=True).encode()).hexdigest()
command = ['sh', str(h / 'tools/run-joint.sh'), str(attempt), module, 'J', '7000', '7', fp]
record = dict(attempt=attempt, module=module, source_revision=revision, source_sha256=sha(src),
              deps_fingerprint=fp, dependencies=deps, environment=env, environment_sha256=sha(envp),
              command=command, caps=dict(MemoryHigh='5G', MemoryMax='7G', MemorySwapMax=0),
              source_path=str(src))
private.mkdir(exist_ok=True)
(private / 'preflight.json').write_text(json.dumps(record,indent=2)+'\n')
r = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(private / 'launcher-9500.log').write_text(r.stdout)
record['launcher_exit'] = r.returncode
for name in ['out-9500.log','time-9500.log','sha-9500.txt']:
    p = t / name
    if p.exists():
        (private / name).write_bytes(p.read_bytes())
        record[name] = p.read_text()
if 'out-9500.log' in record:
    record['axioms_lines'] = [l for l in record['out-9500.log'].splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l]
if 'time-9500.log' in record:
    timing = record['time-9500.log']
    record['exit_status'] = int(re.search(r'Exit status: (\d+)', timing).group(1))
    record['wall_time'] = re.search(r'Elapsed .*: ([0-9:.]+)', timing).group(1)
    record['peak_rss_kib'] = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', timing).group(1))
    record['swaps'] = int(re.search(r'Swaps: (\d+)', timing).group(1))
obj = j / 'objects' / (module + '.olean')
if obj.exists():
    record['output_object'] = dict(sha256=sha(obj), size=obj.stat().st_size)
record['dependencies_unchanged_after'] = all(sha(pathlib.Path(d['object_path'])) == d['object_sha256'] for d in deps)
(private / 'receipt-9500.json').write_text(json.dumps(record,indent=2)+'\n')
print(r.stdout)
sys.exit(r.returncode)
