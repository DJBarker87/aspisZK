from pathlib import Path
import hashlib, json, re
p = Path(__file__).resolve().parent
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
m = json.loads((p / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert m['compiled_objects_included'] is False
assert m['entry']['role'] == 'audited_main'
e = m['entry']
src = p / e['source']
rec = json.loads((p / e['receipt']).read_text())
pre = json.loads((p / e['preflight']).read_text())
cmd = json.loads((p / e['command']).read_text())
profile = p / e['profile']
log = (p / e['log']).read_text()
assert src.is_file() and sha(src) == e['source_sha256'] == rec['source_sha256'] == pre['source_sha256']
assert rec == e['launch_metrics'] and rec['exit_status'] == 0 and rec['process_swaps'] == 0
assert rec['watchdog_abort'] is None and rec['foreign_lean_samples'] == [] and rec['object_sha256'] == e['object_sha256']
assert pre['source_revision'] == rec['source_revision_at_launch'] and pre['no_dependency_builds'] is True
assert sha(profile) == pre['profile_sha256']
assert e['direct_imports'] == pre['direct_imports']
assert 'LEAN_PATH=' + profile.read_text().strip() in cmd['argv']
assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M') + 1] == '4400'
for imp in e['direct_imports'].values():
    q = Path(imp['path'])
    assert q.is_file() and sha(q) == imp['sha256'], imp['path']
text = re.sub(r'/\-.*?\-/', '', src.read_text(), flags=re.S)
text = re.sub(r'--[^\n]*', '', text)
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', text)
for theorem, axioms in e['theorems'].items():
    reports = re.findall("'" + re.escape(theorem) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
    assert len(reports) == 1, theorem
    got = set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', reports[0]))
    assert got == set(axioms) and got <= {'propext', 'Classical.choice', 'Quot.sound'}
failed = json.loads((p / m['failed_attempts_file']).read_text())
assert all(x['accepted'] is False for x in failed)
for ext in ('*.olean', '*.ilean', '*.pyc', '*.so', '*.dylib', '*.elf'):
    assert not list(p.rglob(ext)), ext
for line in (p / 'SHA256SUMS').read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(p / rel) == digest, rel
print('PASS: exact source, receipt, preflight, profile, imports, standard-only axiom reports, failed-attempt labels, and source-only contents')
