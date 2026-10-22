#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m = json.loads((HERE / 'manifest.json').read_text())
r = json.loads((HERE / m['launch_receipt']).read_text())
pre = json.loads((HERE / m['preflight']).read_text())
cmd = json.loads((HERE / m['launch_command']).read_text())
log = (HERE / m['lean_raw_log']).read_text()
src = HERE / m['source']
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert sha(src) == m['source_sha256'] == r['source_sha256'] == pre['source_sha256']
assert r == m['launch_metrics'] and r['exit_status'] == 0 and r['watchdog_abort'] is None
assert r['process_swaps'] == 0
assert r['object_sha256'] == m['external_object_sha256']
assert r['source_revision_at_launch'] == pre['source_revision'] == m['source_revision_at_launch']
assert 'LEAN_PATH=' + (HERE / m['profile']).read_text().strip() in cmd['argv']
assert '-M' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M') + 1] == '4400'
assert '-j1' in cmd['argv']
for d in m['dependencies']:
    assert sha(HERE / d['source']) == d['source_sha256']
    assert pre['direct_imports'][d['module']] == {'path':d['path'], 'sha256':d['sha256']}
for name, axioms in m['theorems'].items():
    pattern = "'" + re.escape(m['namespace'] + '.' + name) + r"' depends on axioms:\s*\[(.*?)\]"
    found = re.findall(pattern, log, re.S)
    assert len(found) == 1, name
    assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', found[0])) == set(axioms)
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'sorryAx' not in log and not re.search(r': error(?:\(|:)', log)
text = src.read_text()
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', text, flags=re.S))
assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)', text)
# The small complete helper is immutable here. Whole-source equality is not claimed.
raw = (REPO / 'crates/aspis-r1-cost-probe/src/weights.rs').read_text()
needle = 'fn factored_s2_libra_weights('
start = raw.index(needle)
brace = raw.index('{', start)
depth = 0
for end in range(brace, len(raw)):
    if raw[end] == '{': depth += 1
    elif raw[end] == '}':
        depth -= 1
        if depth == 0: break
helper = raw[start:end+1].encode()
assert hashlib.sha256(helper).hexdigest() == m['source_body_hash']
assert helper == (HERE / 'source-pins/factored_s2_libra_weights.rs').read_bytes()
assert m['compiled_objects_included'] is False
for suffix in ['*.olean', '*.elf', '*.so', '*.pyc']:
    assert not list(HERE.rglob(suffix)), suffix
for line in (HERE / 'SHA256SUMS').read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(HERE / rel) == digest, rel
print('PASS: S9 decoded side-update algebra, standard axioms, receipts and helper pin; source execution remains OPEN')
