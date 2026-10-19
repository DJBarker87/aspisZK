from pathlib import Path
import hashlib, io, json, re, tarfile

b = Path('/home/dombarker/project-offloads/aspis-r1-j1a-decoder-no-unwrap-regression-20261016')
sha = lambda data: hashlib.sha256(data).hexdigest()
files = {}
for rel in ['run.py', 'before-manifest.json', 'after-manifest.json', 'baseline-reuse.json']:
    files[rel] = (b / rel).read_bytes()
for folder in ['runs', 'cu-comparison-1']:
    for p in sorted((b / folder).rglob('*')):
        if p.is_file() and p.suffix != '.key':
            assert p.suffix in ['.json', '.bin', '.py', '.log'], p
            files[str(p.relative_to(b))] = p.read_bytes()
for rel in ['before-sbf/aspis_r1_cost_probe_program.so', 'after-sbf-fresh-artifacts/aspis_r1_cost_probe_program.so']:
    files[rel] = (b / rel).read_bytes()
pins = json.loads(files['after-manifest.json'])
for rel, digest in pins['files'].items():
    assert sha((b / 'after' / rel).read_bytes()) == digest, rel
targets = {}
for name in ['before-sbf', 'after-counter', 'after-sbf-fresh', 'cu-pair']:
    receipt = json.loads(files['runs/' + name + '/receipt.json'])
    timing = files['runs/' + name + '/time.log'].decode()
    value = lambda label: int(re.search(re.escape(label) + r':\s*(\d+)', timing)[1])
    targets[name] = {k: receipt[k] for k in ['exit', 'wall_seconds', 'cgroup_peak_bytes', 'swap_current_bytes', 'source_revision']}
    targets[name].update(peak_rss_kib=value('Maximum resident set size (kbytes)'), swaps=value('Swaps'), reused=name == 'before-sbf')
summary = {
    'targets': targets,
    'comparison': json.loads(files['cu-comparison-1/comparison.json']),
    'baseline_elf_sha256': sha(files['before-sbf/aspis_r1_cost_probe_program.so']),
    'candidate_elf_sha256': sha(files['after-sbf-fresh-artifacts/aspis_r1_cost_probe_program.so']),
    'baseline_reuse': json.loads(files['baseline-reuse.json']),
    'key_retention': 'Payer/checkpoint and generated artifact keys retained on host, excluded from this archive.',
    'axioms': 'Not applicable: Rust execution evidence only.',
    'scope': 'One saved transfer1023 fixture, [3,10] and ASQ8, same initial accounts; setup excluded. No universal call-count, custody, stack-safety or compiler-correctness claim.',
    'stack_diagnostics': 'Existing point_claims stack-offset diagnostics remain in build logs.',
}
files['SUMMARY.json'] = (json.dumps(summary, indent=2) + '\n').encode()
files['collect-regression.py'] = Path(__file__).read_bytes()
manifest = {n: {'bytes': len(d), 'sha256': sha(d)} for n, d in files.items()}
files['archive-members.json'] = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
dest = b / 'decoder-no-unwrap-regression-evidence.tar.gz'
assert not dest.exists()
with tarfile.open(dest, 'w:gz') as tf:
    for name, data in sorted(files.items()):
        info = tarfile.TarInfo(name); info.size = len(data); info.mode = 0o644
        tf.addfile(info, io.BytesIO(data))
(b / 'SUMMARY.json').write_bytes(files['SUMMARY.json'])
print(json.dumps({'archive': str(dest), 'sha256': sha(dest.read_bytes()), 'bytes': dest.stat().st_size, 'members': len(files), 'summary': summary}, sort_keys=True))
