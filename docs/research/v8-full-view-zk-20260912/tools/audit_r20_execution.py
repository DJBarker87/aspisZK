#!/usr/bin/env python3
"""Recompute an R20 finite-run receipt from raw SVM logs and pinned metadata.

This does not prove source equivalence or security. A valid evidence audit can
and currently must produce a FAILING under-1M benchmark receipt.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

BASE = 'c9315d8b05efb2cdad976bb0f4db3574f1c24577'
FIXTURES = {
    'world0': '0f90e0670d5c7cedf1bea159640016eeec1574ac0de89dc94d83dd9255f07da7',
    'world1-resumed': 'ca868e8f9495e06368ecaa712486befecbfaadc6ab38e8caddf38e368134ca71',
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def checkpoints(logs):
    out = {}
    for i, line in enumerate(logs[:-1]):
        if line.startswith('Program log: '):
            match = re.fullmatch(r'Program consumption: (\d+) units remaining', logs[i+1])
            if match:
                label = line.removeprefix('Program log: ')
                assert label not in out, label
                out[label] = int(match[1])
    return out

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--evidence', type=Path, required=True)
    p.add_argument('--implementation-commit', required=True)
    p.add_argument('--elf-sha256', required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    assert re.fullmatch('[0-9a-f]{40}', a.implementation_commit)
    assert re.fullmatch('[0-9a-f]{64}', a.elf_sha256)
    m = json.loads((a.evidence/'r18-stage.json').read_text())
    r20 = m['r20_execution']
    assert r20['base_git_commit'] == BASE
    assert r20['protocol_unchanged'] and not r20['arithmetic_only_not_verifier']
    assert m['profile'] == 'AV8/R19/sparseG-T163/quadratic-channel-fold/research-v1'
    for name, change in r20['source_changes'].items():
        assert m['files'][name] == change['after'], name
    probe = json.loads((a.evidence/'r17-sbf-probe.json').read_text())
    if not r20['instrumented']:
        assert probe['diagnostic_instrumentation'] is False
    cases, reports = [], {}
    for world, fixture_hash in FIXTURES.items():
        logs = list(a.evidence.glob('*svm-'+world+'.log'))
        assert len(logs) == 1, logs
        raw = logs[0].read_text()
        assert 'Exit status: 0' in raw
        rows = [json.loads(line) for line in raw.splitlines() if line.startswith('{')]
        assert len(rows) == 4
        keyed = {(r['limit_class'], r['case']): r for r in rows}
        assert len(keyed) == 4
        for kind, cap in [('acceptance',1_000_000),('diagnostic',100_000_000)]:
            for name in ['honest','bad-combined-final']:
                row = keyed[kind,name]
                assert row['cu_limit'] == cap and row['heap_bytes'] == 262144
                assert row['unchanged_accounts']
                assert 0 <= row['cu'] <= cap
                if row['resource_failure']:
                    assert not row['accepted'] and not row['custom_rejection']
                if kind == 'diagnostic':
                    assert not row['resource_failure']
                    assert row['accepted'] if name == 'honest' else row['custom_rejection']
                if not r20['instrumented']:
                    assert not checkpoints(row['logs']), 'profiling survived in clean ELF'
                if kind == 'acceptance':
                    cases.append({
                        'world': world, 'case': name,
                        'kind': 'honest' if name == 'honest' else 'negative',
                        'fixture_sha256': fixture_hash,
                        'cu_limit': cap, 'cu': row['cu'],
                        'complete': row['accepted'] or row['custom_rejection'],
                        'accepted': row['accepted'], 'resource_failure': row['resource_failure'],
                    })
        honest = keyed['diagnostic','honest']
        cps = checkpoints(honest['logs'])
        pairs = [
            ('semantic_rounds','R17:semantic-start','v8:semantic-rounds'),
            ('semantic_total','R17:semantic-start','R17:semantic-end'),
            ('prepare','R17:semantic-end','R17:prepare-end'),
            ('ordinary','R19:tail-folds-end','R19:ordinary-end'),
            ('G_and_final','R19:ordinary-end','R19:primary-terminal-accepted'),
        ]
        reports[world] = {'raw_log_sha256': sha(logs[0]), 'fixture_sha256': fixture_hash,
            'honest_diagnostic_cu': honest['cu'],
            'intervals': {n:cps[s]-cps[e] for n,s,e in pairs if s in cps and e in cps},
            'checkpoints_remaining': cps}
    receipt = {
        'commit_sha': a.implementation_commit, 'base_commit_sha': BASE,
        'elf_sha256': a.elf_sha256, 'source_manifest_sha256': sha(a.evidence/'r18-stage.json'),
        'scope': 'complete-primary-verifier', 'instrumented': r20['instrumented'],
        'heap_bytes': 262144, 'same_profile': True, 'cases': cases,
        'diagnostic_not_budget_evidence': reports,
        'additional_independent_fixtures_run': False,
        'privacy_proved': False, 'soundness_proved': False,
    }
    assert not a.output.exists(), 'do not overwrite evidence'
    a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'evidence_audit':'PASS','receipt':str(a.output),
        'under_1m_claim':False,'runs':reports},indent=2))

if __name__ == '__main__':
    main()
