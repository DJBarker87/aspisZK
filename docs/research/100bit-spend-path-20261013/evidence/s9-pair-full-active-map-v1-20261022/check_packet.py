from pathlib import Path
import hashlib, json, re
p = Path(__file__).resolve().parent
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
m = json.loads((p / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert m['compiled_objects_included'] is False
assert m['entry']['role'] == 'audited_main'

def check_run(run, verify_import_files):
    src = p / run['source']
    rec = json.loads((p / run['receipt']).read_text())
    pre = json.loads((p / run['preflight']).read_text())
    cmd = json.loads((p / run['command']).read_text())
    log = (p / run['log']).read_text()
    assert src.is_file() and sha(src) == run['source_sha256'] == rec['source_sha256'] == pre['source_sha256']
    assert rec == run['launch_metrics'] and rec['exit_status'] == 0
    assert rec.get('process_swaps', 0) == 0 and rec.get('scope_swap_peak_bytes', 0) == 0
    assert rec['watchdog_abort'] is None
    assert rec['object_sha256'] == run['object_sha256']
    assert pre['no_dependency_builds'] is True if 'no_dependency_builds' in pre else True
    assert run['direct_imports'] == pre['direct_imports']
    for theorem, axioms in run['theorems'].items():
        reports = re.findall("'" + re.escape(theorem) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
        assert len(reports) == 1, theorem
        got = set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', reports[0]))
        assert got == set(axioms) and got <= {'propext', 'Classical.choice', 'Quot.sound'}
    return pre, cmd

e = m['entry']
pre, cmd = check_run(e, True)
profile = p / e['profile']
assert sha(profile) == pre['profile_sha256']
assert 'LEAN_PATH=' + profile.read_text().strip() in cmd['argv']
assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M') + 1] == '4400'
for imp in e['direct_imports'].values():
    q = Path(imp['path'])
    assert q.is_file() and sha(q) == imp['sha256'], imp['path']
# Verify the separately retained NUC prefix source/run receipt; the imported OLean remains external.
d = m['dependencies']['S9PairCallerActiveBodyMapV1']
pre_d, cmd_d = check_run(d, False)
assert d['role'] == 'audited_dependency_source_only'
assert d['source_sha256'] == '521a08a114b34371a05e6a55dd020a40ccc9ab623f66fe5341f15a48e5a6a912'
assert d['object_sha256'] == e['direct_imports']['S9PairCallerActiveBodyMapV1']['sha256']
assert d['launch_metrics']['scope_swap_peak_bytes'] == 0
assert pre_d['limits']['memory.swap.max'] == '0'
# No proof escapes, binaries, generated caches, or compiled Lean objects in this source-only packet.
for run in (e, d):
    text = re.sub(r'/\-.*?\-/', '', (p / run['source']).read_text(), flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', text)
for ext in ('*.olean', '*.ilean', '*.pyc', '*.so', '*.dylib', '*.elf'):
    assert not list(p.rglob(ext)), ext
for line in (p / 'SHA256SUMS').read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(p / rel) == digest, rel
print('PASS: main and retained NUC prefix sources, receipts, profiles, object pins, standard-only axiom reports, and source-only contents')
