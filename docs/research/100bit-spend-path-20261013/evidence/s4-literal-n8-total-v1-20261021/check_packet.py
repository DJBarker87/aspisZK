from pathlib import Path
import hashlib, json, re
D = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m = json.loads((D / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1'
for f in m['files']:
    p = D / f['path']
    assert p.is_file() and sha(p) == f['sha256'], f['path']
for entry in m['modules']:
    src = D / entry['source']
    rc = json.loads((D / entry['receipt']).read_text())
    cmd = json.loads((D / entry['command']).read_text())
    assert sha(src) == entry['source_sha256'] == rc['source_sha256'] == cmd['source_sha256']
    assert entry['object_sha256'] == rc['object_sha256'] == cmd['object_sha256']
    assert entry['source_revision'] == rc['source_revision'] == cmd['launch_git_revision']
    assert rc['exit_status'] == cmd['exit_status'] == entry['exit_status'] == 0
    assert cmd['resource']['swap_bytes'] == 0 and cmd['resource']['lean_memory_mb'] == 4400
    assert '-j1' in cmd['argv'] and '-M' in cmd['argv']
    assert cmd['resource']['peak_rss_bytes'] < 8 * 2**30
    log = (D / 'evidence/lean.log').read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    reports = re.findall(r'depends on axioms:\s*\[([^]]*)\]', log)
    assert len(reports) == 3
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for report in reports:
        assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', report)) <= allowed
    assert not re.search(r'\b(sorry|axiom|native_decide)\b', src.read_text())
for name, owner in m['direct_import_source_map'].items():
    src = D / owner['source']
    assert src.is_file() and sha(src) == owner['source_sha256'], name
    if 'producer_packet' in owner:
        producer = Path(__file__).resolve().parents[2] / owner['producer_packet']
        receipt = Path(__file__).resolve().parents[2] / owner['producer_receipt']
        assert producer.is_file() and receipt.is_file(), name
assert not any(p.suffix in {'.olean', '.ilean', '.ir', '.o', '.llbc'} for p in D.rglob('*') if p.is_file())
print('PASS: literal N8 totality packet hashes, evidence and standard axiom audit')
