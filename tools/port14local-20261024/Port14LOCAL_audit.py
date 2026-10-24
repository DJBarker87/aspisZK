#!/usr/bin/env python3
"""Read-only source/receipt audit; no Lean launch or native adoption claim."""
import collections
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN = ROOT / 'docs/research/100bit-spend-path-20261013/lean'
OUT = ROOT / 'evidence/port14local-20261024'


def identity(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(ROOT)), 'sha256': hashlib.sha256(data).hexdigest(),
            'bytes': len(data)}


def main():
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    flow = (LEAN / 'VTop_Flow.lean').read_text()
    sections = {}
    expected = {
        'tx1': [16,3,4,13,1,7,12,13,15,14,5,13,11,10,6,9,8,13],
        'tx2_common': [18,16,17,13,23,22,2,0,15,14,5,13,11,10,6,9,21,20,19],
        'tx2_authenticated': [3,13],
    }
    for name, sequence in expected.items():
        match = re.search(r'^def ' + name + r'\b.*?(?=^def |^end AspisR1)', flow,
                          re.MULTILINE | re.DOTALL)
        assert match, name
        body = match.group()
        sites = [{'operation': int(m.group(1)),
                  'line': flow[:match.start()+m.start()].count('\n')+1}
                 for m in re.finditer(r'effects\.op(\d+)\b', body)]
        assert [s['operation'] for s in sites] == sequence, (name, sites)
        assert not re.search(r'\b(?:while|for|loop)\b', body), name
        sections[name] = {'syntactic_sites': sites,
                          'qualification': 'static straight-line sites; kernel execution partition NOT proved'}
    library = [0,1,2,13,14,15,16,20,21,22,23,24]
    stages = (LEAN / 'VTop_OracleStages.lean').read_text()
    assert 'def libraryIds : List Nat := [' + ','.join(map(str, library)) + ']' in stages
    all_sites = expected['tx1'] + expected['tx2_authenticated'] + expected['tx2_common']
    delegated = collections.Counter(i for i in all_sites if i not in library and i not in [5,8,18])
    assert dict(delegated) == {3:2,4:1,7:1,12:1,11:2,10:2,6:2,9:2,17:1,19:1}

    selected = {
        'Port13GATE_Authenticated': ('port13gate', 2),
        'Port13GATE_Canonical': ('port13gate', 1),
        'Port13GATE_Audit': ('port13gate', 5),
        'Port10AUTH_Tree': ('port10auth', 44),
        'Port10AUTH_Node': ('port10auth', 19),
        'Port10AUTH_Leaf': ('port10auth', 12),
        'Port10AUTH_Installed': ('port10auth', 52),
        'Port9OR_Code': ('port9oracle', 4),
        'Port9OR_P6Node': ('port9oracle', 17),
        'Port12COUNT_Installed': ('port12count', 26),
    }
    reused = []
    for module, (job, attempt) in selected.items():
        folder = ROOT / f'evidence/{job}-20261024/lean-{attempt:03}'
        receipt_path = folder / 'receipt.json'
        receipt = json.loads(receipt_path.read_text())
        source = identity(LEAN / f'{module}.lean')
        snapshot = identity(folder / f'sources/{module}.lean')
        assert source['sha256'] == snapshot['sha256'], module
        assert receipt['source_hashes'][f'{module}.lean'] == source['sha256'], module
        assert receipt['exit_status'] == 0, module
        assert receipt['print_axioms'], module
        reused.append({'module': module, 'source': source, 'historical_source': snapshot,
                       'receipt': identity(receipt_path),
                       'historical_result': {key: receipt[key] for key in
                           ['command','source_revision','deps_fingerprint','exit_status',
                            'wall_seconds','peak_rss_kib','swaps','print_axioms']},
                       'assessment': 'source-identical historical focused result; no current host object or release identity check'})

    # Explicitly bounded inventory; no worktree/candidate discovery or reads.
    names = set(selected) | {
        'MultiproofConeP6Callbacks','MultiproofConeP6Batch','MultiproofConeP6Frozen2Stage',
        'MultiproofConePhysicalProgram','MultiproofConePhysicalDigest',
        'Port10AUTH_Total','Port10AUTH_Selected','Port10AUTH_Leaves','Port10AUTH_Tail',
        'Port4B_PhysicalCalls','Port4B_LeafCode','Port4B_NativeLeaf','Port4B_LeafStep',
        'Port4B_LeafInstall','Port4B_VerifyInstall','Port4B_Install','Port9OR_Bodies',
        'Port9OR_Installed','Port9OR_Rejection','Port1_Driver','Port1_Library',
        'Port11PROV_FirstBoth','Port11PROV_Parser','Port6AUTH_Recovery',
        'Port6AUTH_Prefix','Port6AUTH_Probability','Port6AUTH_Accounting',
        'OraclePortRuntimeBindingC7','RawRecordedOracleExtractionMassBin',
        'VTop_Flow','VTop_Trace','VTop_OracleCode','VTop_OracleStages'}
    sources = {name: {**identity(LEAN / f'{name}.lean'),
                     'imports': re.findall(r'^import (.+)$', (LEAN / f'{name}.lean').read_text(), re.MULTILINE)}
               for name in sorted(names)}
    audit = {'status': 'static source audit, not a kernel proof', 'source_revision': revision,
             'flow': sections, 'library_ids': library,
             'owned_maximum_sites': {'batch0':1,'writer':1,'reader':1,'batch1':1},
             'owned_budget_reused': 1046, 'delegated_multiplicities': dict(sorted(delegated.items())),
             'delegated_budget_proved': False, 'full_driver_partition_proved': False,
             'full_driver_1161_proved': False, 'sources': sources, 'reused': reused,
             'new_lean_attempts': 0, 'new_prelean_reservations': 0,
             'scope': 'committed assigned-worktree sources and historical root evidence only'}
    encoded = json.dumps(audit, indent=2) + '\n'
    assert len(encoded.encode()) <= 5_000_000
    (OUT / 'source-audit.json').write_text(encoded)
    endpoint = (LEAN / 'Port13GATE_Authenticated.lean').read_text()
    statement = endpoint[endpoint.index('theorem accepted '):endpoint.index(' := by')]
    assert 'occupied' not in statement[statement.index('(sourceAccepted :'):]
    assert 'sibling' not in statement[statement.index('(sourceAccepted :'):]
    assert 'leafGate' not in statement[statement.index('(sourceAccepted :'):]
    (OUT / 'unchanged-endpoint-statement.txt').write_text(statement + '\n')
    signatures = '\n\n'.join(f'-- {name}; unchanged source, not a new theorem\n' +
                            (LEAN / f'{name}.lean').read_text()
                            for name in ['VTop_Trace','VTop_OracleCode','OraclePortRuntimeBindingC7',
                                         'RawRecordedOracleExtractionMassBin'])
    (OUT / 'retained-interfaces.lean.txt').write_text(signatures)
    print(json.dumps({'passed': True, 'source_files': len(sources),
                      'source_identical_reused_receipts': len(reused),
                      'delegated_multiplicities': dict(sorted(delegated.items())),
                      'new_lean_attempts': 0}))


if __name__ == '__main__':
    main()
