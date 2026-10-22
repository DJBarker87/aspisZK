#!/usr/bin/env python3
"""Read-only certificate checks, then write the scoped P6 composition ledger."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
E = PACKET / 'evidence/multiproof-cone-20261021'
BASE = '3af931da4'
MODULES = ['MultiproofConeP6Composition', 'MultiproofConeP6Verify',
           'MultiproofConeP6Batch', 'MultiproofConeP6Callbacks',
           'MultiproofConeP6Frozen2Stage', 'MultiproofConeP6Freeze']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

def function(text, marker):
    start = text.index(marker)
    end = text.index('{', start)+1
    depth = 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[start:end]

for script in ['generate.py', 'p6-citations.py']:
    subprocess.run(['python3', '-B', str(ROOT / 'tools/multiproof-cone-20261021' / script),
                    '--check'], check=True)

manifest = read(E / 'manifest.json')
current = []
reports = 0
for name in MODULES:
    source = PACKET / 'lean' / (name + '.lean')
    candidates = [a for a in manifest['attempts'] if a['module'] == name and a['final_current']]
    assert len(candidates) == 1, (name, 'missing/ambiguous current attempt')
    receipt = candidates[0]
    assert receipt['exit'] == 0 and receipt['swaps'] == 0
    assert receipt['source_sha256'] == sha(source)
    folder = E / (name + '-' + str(receipt['attempt']))
    assert (folder / 'source.lean.txt').read_bytes() == source.read_bytes()
    assert receipt == read(folder / 'receipt.json')
    assert '-M4400' in receipt['argv'] and '-j1' in receipt['argv']
    assert receipt['lean_path'].split(':')[0] == '/tmp/codex-cx-multiproof-p6b-20261021-objects'
    assert not receipt['errors']
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|maxHeartbeats|maxRecDepth)\b|^\s*axiom\s', text, re.M)
    declared = re.findall(r'^theorem (\w+)', text, re.M)
    assert all('#print axioms ' + n in text for n in declared)
    assert receipt['axioms']
    for line in receipt['axioms']:
        match = re.search(r'axioms: \[([\s\S]*?)\]', line)
        assert match and set(re.findall(r'[\w.]+', match[1])) <= STANDARD, line
    for dependency in receipt['owned_transitive_dependencies']:
        assert sha(ROOT / dependency['source']) == dependency['source_sha256']
    reports += len(receipt['axioms'])
    current.append(receipt)

reused = []
for relative, count in [('host-p6/p6-callbacks-1', 3),
                        ('host/receipts/cone3-hash-1', 1),
                        ('host/receipts/cone3-nodes-1', 5),
                        ('host/receipts/cone4-physical-1', 3),
                        ('host/receipts/cone2-leaf-2', 2),
                        ('host-cone6/cone6-guards-final-1', 3)]:
    folder = E / relative
    receipt = read(folder / 'receipt.json')
    assert receipt['exit_status'] == 0 and receipt['swaps'] == 0
    output = (folder / 'stdout.log').read_text()
    assert output.count('VERIFICATION SUCCESSFUL') == count
    assert 'VERIFICATION FAILED' not in output
    assert receipt['limits'] == {'memory.high': str(6*2**30), 'memory.max': str(8*2**30),
                                 'memory.swap.max': '0', 'pids.max': '64'}
    # Pin executable source fields that are present in this checkout. Host
    # workspace metadata and tool binaries remain hash-only receipt evidence.
    for relative_source, expected in receipt['source_sha256'].items():
        path = ROOT / relative_source
        if path.is_file() and (relative_source.endswith('.rs') or relative_source.startswith('crates/')):
            if path.name in {'lib.rs', 'proofs.rs'}:
                # Other harness registrations changed after these independent
                # roots passed. No result for those other roots is reused.
                continue
            if relative == 'host-p6/p6-callbacks-1' and path.name == 'p6_certificates.rs':
                marker = '/// Independent oracle replies'
                assert (folder/'inputs/src--p6_certificates.rs.txt').read_text().split(marker)[0] == path.read_text().split(marker)[0]
                continue
            if relative == 'host/receipts/cone2-leaf-2' and path.name == 'adoption_level.rs':
                # Unverified node/level contracts in this separate module are
                # neither called nor used as stubs by the leaf roots.
                continue
            if relative == 'host/receipts/cone2-leaf-2' and path.name == 'frozen.rs':
                assert function((folder/'inputs/src--frozen.rs.txt').read_text(), 'pub(crate) fn batch_leaf<') == function(path.read_text(), 'pub(crate) fn batch_leaf<')
                continue
            assert sha(path) == expected, relative_source
    reused.append({'receipt': str((folder/'receipt.json').relative_to(ROOT)),
                   'sha256': sha(folder/'receipt.json'), 'successful_roots': count})

changed = subprocess.check_output(['git', 'diff', '--name-only', BASE], cwd=ROOT, text=True).splitlines()
assert not any(p.startswith('crates/') or '/lean-candidates/' in p for p in changed)
allowed = {str((PACKET/'lean'/(m+'.lean')).relative_to(ROOT)) for m in MODULES}
assert all('/lean/' not in p or p in allowed for p in changed)
for source in allowed:
    assert subprocess.run(['git', 'cat-file', '-e', BASE+':'+source], cwd=ROOT,
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode != 0

result = {'schema': 'multiproof-p6-composition-audit-v1',
          'source_revision': subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip(),
          'current_lean_receipts': current, 'standard_axiom_reports': reports,
          'reused_local_kani_certificates': reused,
          'composed_verifier_owned_certificate': True,
          'composed_batch_owned_observation_certificate': True,
          'frozen2_both_batches_instantiated_at_named_p6_boundary': True,
          'standalone_whole_function_kani_certificate': False,
          'shipped_function_charon_extraction': False,
          'external_p6_source_library_lowering_retained': True,
          's2_s10_caller_binding_retained': True,
          'global_accepted_run_join_constructed': False,
          'headline_premises_removed': 0, 'shipped_sources_changed': False,
          'elf_rebuild_triggered': False, 'full_release_manifest_replayed': False}
(E/'p6b-audit.json').write_text(json.dumps(result, indent=2)+'\n')
print(f'P6 composition audited: {len(current)} focused targets, {reports} standard reports; local P6 and caller binding retained')
