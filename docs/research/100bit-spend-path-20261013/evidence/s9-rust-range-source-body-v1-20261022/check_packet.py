#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re
p = Path(__file__).resolve().parent
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
m = json.loads((p / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert m['compiled_objects_included'] is False
for e in m['entries']:
    r = json.loads((p / e['receipt']).read_text())
    pre = json.loads((p / e['preflight']).read_text())
    cmd = json.loads((p / e['command']).read_text())
    log = (p / e['log']).read_text()
    s = (p / e['source']).read_text()
    assert r == e['launch_metrics'] and r['exit_status'] == 0 and r['process_swaps'] == 0
    assert r['watchdog_abort'] is None and r['foreign_lean_samples'] == []
    assert sha(p / e['source']) == e['source_sha256'] == r['source_sha256'] == pre['source_sha256']
    assert r['object_sha256'] == e['object_sha256']
    assert r['source_revision_at_launch'] == pre['source_revision']
    assert pre['direct_imports']['S9FixedIteratorTransitionsV1']['sha256'] == '0eb3192b0357c640080005f48093436e45beb9d6d5cbc478f893e08bde0dc800'
    assert pre['controller_sha256'] == '9b827933f26ff248491bf1fd187e6d43b804686512bd49b8edacf8ea6416fab0'
    assert 'LEAN_PATH=' + (p / e['profile']).read_text().strip() in cmd['argv']
    assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M') + 1] == '4400'
    for name, ax in e['theorems'].items():
        reports = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
        assert len(reports) == 1, name
        got = set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', reports[0]))
        assert got == set(ax) and got <= {'propext', 'Classical.choice', 'Quot.sound'}
    uncommented = re.sub(r'/\-.*?\-/', '', s, flags=re.S)
    uncommented = re.sub(r'--[^\n]*', '', uncommented)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', uncommented)
    assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)', uncommented)
for ext in ('*.olean', '*.elf', '*.so', '*.pyc'):
    assert not list(p.rglob(ext))
for line in (p / 'SHA256SUMS').read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(p / rel) == digest, rel
assert (p / m['references']['source_comparison_packet']).exists()
print('PASS: schema, source/receipt/object/import pins, focused command and standard axiom reports; binary/runtime refinement remains open')
