#!/usr/bin/env python3
"""Read-only proof/receipt audit; no compilation, solver or release replay."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
OUT = PACKET / 'evidence/join-split-draft-20261021'
BASE = '3a01b2d6d'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


subprocess.run(['python3', '-B', str(Path(__file__).with_name('signatures.py'))], check=True)
manifest = json.loads((OUT / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
attempts = manifest['attempts']
seen = set()
for attempt in attempts:
    directory = OUT / f"{attempt['module']}-{attempt['attempt']}"
    assert sha(directory / 'source.lean.txt') == attempt['source_sha256']
    receipt = json.loads((directory / 'receipt.json').read_text())
    assert receipt == attempt or all(receipt[k] == v for k, v in attempt.items() if k != 'final_current')
    command = json.loads((directory / 'command.json').read_text())
    for key, value in command.items():
        assert attempt[key] == value
    fingerprint_input = attempt['direct_imports']
    if attempt.get('deps_fingerprint_kind') == 'imports-and-environment-v2':
        if attempt['environment_artifacts']:
            assert sha(directory / 'cache-overlay.json') == attempt['environment_artifacts']['private_cache_overlay_sha256']
        fingerprint_input = {'imports': attempt['direct_imports'], 'lean_path': attempt['lean_path'],
                             'environment_artifacts': attempt['environment_artifacts']}
    fp = hashlib.sha256(json.dumps(fingerprint_input, sort_keys=True).encode()).hexdigest()
    assert fp == attempt['deps_fingerprint']
    unique = (attempt['source_sha256'], fp)
    assert unique not in seen
    seen.add(unique)
    assert attempt['swaps'] == 0
    assert attempt['peak_rss_bytes'] < 8 * 1024**3
    assert all(flag in attempt['argv'] for flag in ['-j1', '-M4400', '-DElab.async=false'])
    assert attempt['wall_seconds'] > 0
    if attempt['exit'] == 0:
        assert not attempt['errors']
        for line in attempt['axioms']:
            if 'depends on axioms:' in line:
                names = set(re.search(r'\[([\s\S]*)\]', line)[1].replace('\n', '').replace(' ', '').split(','))
                assert names <= ALLOWED, (attempt['module'], names)
            else:
                assert 'does not depend on any axioms' in line

frozen = []
theorems = []
for path in sorted((PACKET / 'lean').glob('OraclePortJoinSplit*.lean')):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option (maxRecDepth|maxHeartbeats)',
                         source, re.M)
    accepted = [a for a in attempts if a['module'] == path.stem and a['exit'] == 0
                and a['source_sha256'] == sha(path)]
    assert len(accepted) == 1, path
    accepted = accepted[0]
    assert accepted['final_current']
    for dep in accepted['direct_imports']:
        assert sha(dep['path']) == dep['sha256'], dep
    obj = Path('/tmp/codex-cx-join-split-draft-20261021-objects') / (path.stem + '.olean')
    assert sha(obj) == accepted['object_sha256']
    assert obj.stat().st_size == accepted['object_size']
    names = re.findall(r'^theorem (\w+)', source, re.M)
    namespace = re.search(r'^namespace (\S+)', source, re.M)
    for name in names:
        full = namespace[1] + '.' + name
        assert '#print axioms ' + name in source
        assert any(line.startswith("'" + full + "'") for line in accepted['axioms']), full
        theorems.append(full)
    frozen.append({'module': path.stem, 'path': str(path.relative_to(ROOT)),
                   'sha256': sha(path), 'accepted_attempt': accepted['attempt'],
                   'object_sha256': accepted['object_sha256'], 'object_bytes': accepted['object_size']})

for owner in json.loads((OUT / 'inherited-owner-signatures.json').read_text()):
    path = ROOT / owner['path']
    assert sha(path) == owner['current_source_sha256']
    assert owner['signature'] in path.read_text()
for pin in json.loads((OUT / 'ordering-source-pins.json').read_text()):
    assert sha(ROOT / pin['path']) == pin['current_sha256'] == pin['base_sha256']
    if pin['freeze_revision']:
        assert pin['freeze_byte_identical']
        assert pin['freeze_sha256'] == pin['current_sha256']
for pin in json.loads((OUT / 'cache-overlay.json').read_text())['objects']:
    assert sha(pin['source_object']) == sha(pin['selected_object']) == pin['sha256']
    assert Path(pin['selected_object']).is_symlink()

# All modifications relative to the assigned base are additions in this packet.
diff = subprocess.check_output(['git', 'diff', '--name-status', BASE], text=True)
for row in diff.splitlines():
    status, path = row.split('\t')
    assert status == 'A', row
    assert path.startswith(('tools/oracle-port-join-split/',
                            str(PACKET.relative_to(ROOT) / 'evidence/join-split-draft-20261021/'),
                            str(PACKET.relative_to(ROOT) / 'lean/OraclePortJoinSplit'),
                            str(PACKET.relative_to(ROOT) / 'design/JOIN-SPLIT-DRAFT-20261021.md'))), row
    assert Path(path).suffix not in {'.olean', '.so', '.elf', '.tar', '.gz', '.llbc'}
subprocess.run(['git', 'diff', '--check'], check=True)

freeze = [a for a in attempts if a['module'] == 'OraclePortJoinSplitFreeze' and a['exit'] == 0]
assert len(freeze) == 1
asq8_freeze = [a for a in attempts if a['module'] == 'OraclePortJoinSplitASQ8Freeze' and a['exit'] == 0]
assert len(asq8_freeze) == 1
(OUT / 'frozen-sources.json').write_text(json.dumps(frozen, indent=2) + '\n')
summary = {
    'status': 'focused additive conditional split; frozen source/order/runtime joins remain open',
    'base': BASE, 'modules': len(frozen), 'distinct_theorems': len(theorems),
    'theorems': theorems, 'attempts': len(attempts),
    'successful_attempts': sum(a['exit'] == 0 for a in attempts),
    'retained_failed_attempts': sum(a['exit'] != 0 for a in attempts),
    'accepted_axiom_reports': sum(len(a['axioms']) for a in attempts if a['exit'] == 0),
    'standard_axioms_only': True, 'swaps': 0,
    'peak_rss_bytes_all_attempts': max(a['peak_rss_bytes'] for a in attempts),
    'final_focused_import': {k: freeze[0][k] for k in
        ['module', 'attempt', 'exit', 'wall_seconds', 'peak_rss_bytes', 'swaps']},
    'separate_ASQ8_import': {k: asq8_freeze[0][k] for k in
        ['module', 'attempt', 'exit', 'wall_seconds', 'peak_rss_bytes', 'swaps']},
    'union_import_obstruction': 'AspisR20Request.Types / AspisR1AdapterReconstruct.Types: '
                                'instDiscriminantPoolV1PairLatePublicStatementErrorV1Isize',
    'original_endpoint_premise_removed': False,
    'controlled_split_redundant_execution_deleted': True,
    'coherent_full_frozen_release_replay': False,
}
(OUT / 'audit-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'theorems'}, indent=2))
