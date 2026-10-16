#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess

b = Path(__file__).resolve().parent
root = b.parents[4]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
attempts = {
    'framing-decode-a': ('FS2.DuplexDecode', 0),
    'framing-trailing-a': ('R1TrailingStateFrame', 3),
    'framing-public-a': ('R1PublicInitFrame', 6),
    'framing-record-a': ('R1RecordFrameCodec', 6),
    'framing-length-a': ('R1RecordLengthCodec', 2),
    'framing-model-a': ('R1RecordParserModel', 3),
    'framing-agreement-a': ('ExtractedPrefixFrameAgreement', 2),
    'framing-audit-a': ('ExtractedPrefixFrameAudit', 16),
}
sources = {x['module']: x for x in json.loads((b/'target-source-pins.json').read_text())}
produced = {}
for a, (module, count) in attempts.items():
    d = b/'runs'/a
    r = json.loads((d/'receipt.json').read_text())
    manifest = b/('input-manifest-'+a+'.json')
    m = json.loads(manifest.read_text())
    assert r['target'] == module and r['exit_status'] == 0
    assert r['source_sha256'] == sha(d/'source.lean')
    if module in sources:
        p = sources[module]
        committed = subprocess.check_output(['git', 'show', p['source_revision']+':'+p['source']], cwd=root)
        assert hashlib.sha256(committed).hexdigest() == p['source_sha256'] == r['source_sha256']
        assert committed == (d/'source.lean').read_bytes()
    else:
        p = root/'docs/research/100bit-spend-path-20261013/lean'/(module+'.lean')
        assert p.read_bytes() == (d/'source.lean').read_bytes()
    assert r['runner_sha256'] == sha(d/'runner.py')
    assert r['input_manifest_sha256'] == sha(manifest)
    assert r['limits'] == {'memory.max':'8589934592', 'memory.high':'6442450944', 'memory.swap.max':'0'}
    assert r['process_swaps'] == 0 and r['cgroup_swap_current'] == '0'
    assert r['memory_events_before'] == r['memory_events_after']
    assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
    assert '4.32.0' in r['lean_version'] and len(r['runtime_sha256']) == 4
    assert r['olean_sha256'] is not None
    for old_module, output in produced.items():
        assert m['new_import_objects'][old_module.replace('.', '/')+'.olean'] == output
    produced[module] = r['olean_sha256']
    log = (d/'lean.log').read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    assert len(reports) == count, (a, len(reports), count)
    for _, axioms in reports:
        assert set(x.strip() for x in axioms.split(',')) <= allowed
    assert 'sorryAx' not in log and 'error:' not in log

# Check current cache and the accepted symbolic repair against every new input.
prior = b.parent/'r18-current-framing-closure-20261016'
cache = json.loads((prior/'cache/framing-reuse-audit.json').read_text())['modules']
duplex = json.loads((b.parent/'r18-duplex-symbolic-compat-20261016/runs/framing-duplex-b/receipt.json').read_text())
for a in attempts:
    m = json.loads((b/('input-manifest-'+a+'.json')).read_text())
    for module, e in cache.items():
        assert m['new_import_objects'][module.replace('.', '/')+'.olean'] == e['object_sha256']
    assert m['new_import_objects']['FS2/Duplex.olean'] == duplex['olean_sha256']
    assert m['new_sources']['FS2/Duplex.lean'] == duplex['source_sha256']

# The additional unchanged list-codec predecessor has its producing receipt.
cache = b/'list-field-cache-provenance'
pin = json.loads((cache/'inventory.json').read_text())
r = json.loads((cache/'R1ListFieldCodec.json').read_text())
assert sha(cache/'R1ListFieldCodec.json') == pin['receipt_sha256']
assert sha(cache/'R1ListFieldCodec.lean') == pin['source_sha256'] == r['key']['source_sha256']
assert r['exit_status'] == 0 and r['objects']['.olean']['sha256'] == pin['object_sha256']
assert all(set(x['axioms']) <= allowed for x in r['axioms']['reports'])
for a in ['framing-model-a', 'framing-agreement-a', 'framing-audit-a']:
    m = json.loads((b/('input-manifest-'+a+'.json')).read_text())
    assert m['new_import_objects']['R1ListFieldCodec.olean'] == pin['object_sha256']
    assert m['new_sources']['R1ListFieldCodec.lean'] == pin['source_sha256']
    assert m['new_import_objects']['R1RetainedFieldByteCodec.olean'] == r['key']['imports']['R1RetainedFieldByteCodec']['objects']['.olean']['sha256']
outputs = json.loads((b/'output-object-pins.json').read_text())
assert outputs == produced
for line in (b/'SHA256SUMS').read_text().splitlines():
    h, p = line.split('  ', 1)
    assert sha(b/p) == h, p
print('PASS: eight focused targets; 38 standard-only reports; exact source/runtime/resource pins; current framing and list-codec input receipts; output chain')
