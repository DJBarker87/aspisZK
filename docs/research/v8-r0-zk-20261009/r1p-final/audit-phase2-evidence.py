#!/usr/bin/env python3
"""Audit the final focused-source hashes and theorem evidence without replay."""
import hashlib
import json
import pathlib
import re
import subprocess

root = pathlib.Path(__file__).resolve().parents[1]
records = [json.loads(line) for line in
           (root / 'r1p-final/phase2-attempts-9400-9599.jsonl').read_text().splitlines()]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
modules = sorted((root / 'lean/R1Z').glob('Phase*.lean'))
modules = [p for p in modules if p.name in {
    'PhaseEndpointObstructionBin.lean', 'PhaseMessageDependenciesBin.lean',
    'PhaseMessageEncodingBin.lean', 'PhaseCircleBlocksBin.lean',
    'PhaseSamplerParserBin.lean', 'PhaseLeafEncodingBin.lean',
    'PhaseProtocolInstanceBin.lean'}]
results = []
for src in modules:
    module = 'R1Z/' + src.stem
    digest = hashlib.sha256(src.read_bytes()).hexdigest()
    passing = [r for r in records if r['module'] == module and
               r['source_sha256'] == digest and r['exit'] == 0]
    assert passing, f'no accepted focused compile: {module}'
    record = passing[-1]
    output = record['output']
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output, re.S)
    assert audits, module
    for name, axioms in audits:
        assert set(re.findall(r'[\w.]+', axioms)) <= allowed, (name, axioms)
    text = src.read_text()
    for name in re.findall(r'^theorem (\w+)', text, re.M):
        assert '#print axioms ' + name in text, (module, name)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)', text), module
    results.append({key: record[key] for key in (
        'module', 'attempt', 'source_revision', 'source_sha256', 'deps_fingerprint',
        'exit', 'wall', 'peak_rss_kib', 'swaps') } | {'audits': len(audits)})

endpoint = 'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean'
before = subprocess.check_output(['git', 'show', 'cc4eaf763:' + endpoint])
after = (root / 'lean/R1Z/PrivacyR1Final.lean').read_bytes()
assert before == after, 'final endpoint changed'
result = {
    'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'base_revision': 'cc4eaf763', 'final_endpoint_byte_identical': True,
    'final_endpoint_sha256': hashlib.sha256(after).hexdigest(),
    'attempt_range_valid': all(9400 <= r['attempt'] <= 9599 for r in records),
    'all_attempt_swaps_zero': all(r['swaps'] == '0' for r in records),
    'focused_modules': results,
    'scope': 'Additive model joins and endpoint obstruction; no frozen-manifest release replay.'}
assert result['attempt_range_valid'] and result['all_attempt_swaps_zero']
(root / 'r1p-final/phase2-final-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
