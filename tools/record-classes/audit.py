"""Read-only receipt and source-pin audit; never invokes Lean."""
import hashlib
import json
import pathlib
import re

base = pathlib.Path('docs/research/100bit-spend-path-20261013')
ev = base / 'evidence/record-classes-20261019'
sha = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
manifest = json.loads((ev / 'manifest.json').read_text())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
final = []
for module in ['WireBindingRecordCodec', 'BinWireBindingLengths']:
    src = base / 'lean' / (module + '.lean')
    matches = [r for r in manifest['attempts'] if r['module'] == module and
               r['source_sha256'] == sha(src) and r['exit_status'] == 0]
    assert matches, module
    receipt = matches[-1]
    assert len(receipt['axioms']) == len(re.findall(r'^#print axioms ', src.read_text(), re.M))
    for line in receipt['axioms']:
        if 'depends on axioms:' in line:
            assert set(re.search(r'\[([^]]*)\]', line)[1].split(', ')) <= allowed, line
    for dep in receipt['direct_imports']:
        assert sha(dep['object_path']) == dep['object_sha256'], dep
    final.append(receipt)
remote_final = []
resolved = {m['module']: m for m in json.loads((ev / 'j-dependencies.json').read_text())['modules']}
for r in map(json.loads, (ev / 'j-attempts.jsonl').read_text().splitlines()):
    assert 6300 <= r['attempt'] <= 6319
    assert r['exit'] == 0
    src = (base / 'lean/WireBindingRecordCodec.lean' if r['module'] == 'WireBindingRecordCodec'
           else pathlib.Path('docs/research/v8-r0-zk-20261009/lean/R1Z/WireBindingLengthsR1PBin.lean'))
    if r['attempt'] not in manifest['privacy_final_attempts']:
        continue
    # Earlier successful source is explicitly historical after the literal-domain tightening.
    if r['source_sha256'] != sha(src):
        continue
    assert r['source_sha256'] == resolved[r['module']]['source']['sha256']
    for dep in r['direct_imports']:
        if dep['sha256'] != 'missing':
            actual = next(d for d in resolved[r['module']]['resolved_imports'] if d['module'] == dep['module'])
            assert dep['sha256'] == actual['sha256']
    remote_final.append({'attempt': r['attempt'], 'module': r['module'], 'source_sha256': r['source_sha256'], 'wall': r['wall'], 'peak_rss_kib': r['peak_rss_kib'], 'swaps': r['swaps'], 'axiom_reports': len(r['axioms'])})
    assert len(r['axioms']) == len(re.findall(r'^#print axioms ', src.read_text(), re.M))
    for line in r['axioms']:
        if 'depends on axioms:' in line:
            assert set(re.search(r'\[([^]]*)\]', line)[1].split(', ')) <= allowed, line
assert len(remote_final) == 2
pins = json.loads((ev / 'source-classes.json').read_text())
for pin in pins['pins']:
    assert sha(pin['path']) == pin['sha256'], pin['path']
assert len(pins['sites']) == 31
for module in ['WireBindingRecordCodec', 'BinWireBindingLengths']:
    text = (base / 'lean' / (module + '.lean')).read_text()
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', text)
report = {
    'schema': 'record-classes-audit-v1',
    'local_final_modules': [{'module': r['module'], 'source_sha256': r['source_sha256'],
                             'axiom_reports': len(r['axioms']),
                             'wall_seconds': r['wall_seconds'],
                             'peak_rss_bytes': r['peak_rss_bytes'],
                             'swaps': r['process_swap_count']} for r in final],
    'j_final_modules': remote_final,
    'tx1_syntactic_sites_classified': len(pins['sites']),
    'source_pins_checked': len(pins['pins']),
    'scope': 'Typed codec widths and retained ASF8 decoder; source inventory is not execution refinement.'
}
(ev / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
