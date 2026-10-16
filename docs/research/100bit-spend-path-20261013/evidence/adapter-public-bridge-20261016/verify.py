#!/usr/bin/env python3
"""Read/hash-only verification of the retained focused-check bundle."""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
PREREQUISITE = 'e97ac2bb0275bea5f4f73cdcbb064d45d03df9cd'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


pin = json.loads((HERE / 'archive-pin.json').read_text())
archive = HERE / 'adapter-public-evidence.tar.gz'
assert sha(archive.read_bytes()) == pin['sha256']
assert archive.stat().st_size == pin['bytes']
members = json.loads((HERE / 'archive-members.json').read_text())
with tarfile.open(archive) as tar:
    actual = tar.getmembers()
    assert len(actual) == len(members) == pin['members']
    assert len({m.name for m in actual}) == len(actual)
    assert all(m.isfile() and m.name in members for m in actual)
    def read(name):
        return tar.extractfile(name).read()
    for name, expected in members.items():
        data = read(name)
        assert len(data) == expected['bytes'] and sha(data) == expected['sha256'], name
    manifest = json.loads(read('adapted/sources/SOURCE-MANIFEST.json'))
    reports = 0
    for module, row in manifest['modules'].items():
        data = read('adapted/sources/' + row['stage_as'])
        assert sha(data) == row['source_sha256'], module
        if row['source'].startswith('docs/'):
            path = REPO / row['source']
            committed = path.read_bytes() if path.exists() else subprocess.check_output(
                ['git', 'show', PREREQUISITE + ':' + row['source']], cwd=REPO)
            assert committed == data, module
        receipt = json.loads(read('adapted/successful-targets/' + module + '.json'))
        assert receipt['key']['source_sha256'] == row['source_sha256']
        assert receipt['exit_status'] == 0 and receipt['axioms']['passed']
        assert receipt['process_swaps'] == 0 and receipt['cgroup_swap_current'] == '0'
        assert len(receipt['axioms']['reports']) == row['axiom_requests']
        for report in receipt['axioms']['reports']:
            assert set(report['axioms']) <= ALLOWED, report
            reports += 1
    before = read('joint/runs/original-tags-a/AdapterPaymentDiscriminantAudit/lean.log')
    after = read('adapted/runs/adapter-tags-a/AdapterPaymentDiscriminantAudit/lean.log')
    assert before == after
    summary = json.loads(read('check-summary.json'))
    assert summary == json.loads((HERE / 'check-summary.json').read_text())
    assert sha(before) == summary['discriminant_log_sha256']
    for obj in summary['final_objects'].values():
        assert sha(read('final-artifacts/' + Path(obj['path']).name)) == obj['sha256']
    assert len(summary['final_axioms']['reports']) == 3
assert reports == 24
subprocess.run(['python3', str(HERE.parents[1] / 'tools/adapter-public-discriminant-bridge.py'),
                '--check'], check=True)
print(f'PASS: {len(members)} archive members, {len(manifest["modules"])} target sources/receipts, '
      f'{reports} standard-only reports, identical tags, final object, inverse adapter')
