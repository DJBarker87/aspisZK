#!/usr/bin/env python3
"""Read/hash-only verification; no Lean execution or object substitution."""
import hashlib
import json
from pathlib import Path
import tarfile

HERE = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TARGET = 'ExtractedAdapterWithdrawalBindings'


def sha(data):
    return hashlib.sha256(data).hexdigest()


pin = json.loads((HERE / 'archive-pin.json').read_text())
archive = HERE / 'adapter-bindings-evidence.tar.gz'
assert sha(archive.read_bytes()) == pin['sha256']
assert archive.stat().st_size == pin['bytes']
members = json.loads((HERE / 'archive-members.json').read_text())
prior = HERE.parent / 'adapter-public-bridge-20261016'
oldpin = json.loads((prior / 'archive-pin.json').read_text())
oldarchive = prior / 'adapter-public-evidence.tar.gz'
assert sha(oldarchive.read_bytes()) == oldpin['sha256']
with tarfile.open(archive) as tar, tarfile.open(oldarchive) as old:
    actual = tar.getmembers()
    assert len(actual) == len(members) == pin['members']
    assert len({m.name for m in actual}) == len(actual)
    assert all(m.isfile() and m.name in members for m in actual)
    def read(name):
        return tar.extractfile(name).read()
    for name, expected in members.items():
        data = read(name)
        assert len(data) == expected['bytes'] and sha(data) == expected['sha256'], name
    manifest = json.loads(read('sources/SOURCE-MANIFEST.json'))
    before = json.load(old.extractfile('adapted/sources/SOURCE-MANIFEST.json'))
    for module, row in before['modules'].items():
        assert manifest['modules'][module] == row
        assert read('successful-targets/' + module + '.json') == old.extractfile(
            'adapted/successful-targets/' + module + '.json').read(), module
    row = manifest['modules'][TARGET]
    source = read('sources/' + row['stage_as'])
    assert sha(source) == row['source_sha256']
    assert source == (HERE.parents[1] / 'lean' / (TARGET + '.lean')).read_bytes()
    receipt = json.loads(read('successful-targets/' + TARGET + '.json'))
    assert receipt['key']['source_sha256'] == row['source_sha256']
    assert receipt['exit_status'] == 0 and receipt['axioms']['passed']
    assert len(receipt['axioms']['reports']) == row['axiom_requests'] == 2
    assert receipt['process_swaps'] == 0 and receipt['cgroup_swap_current'] == '0'
    for report in receipt['axioms']['reports']:
        assert set(report['axioms']) <= ALLOWED
    for obj in receipt['objects'].values():
        assert sha(read('final-artifacts/' + Path(obj['path']).name)) == obj['sha256']
    assert json.loads(read('check-summary.json')) == json.loads(
        (HERE / 'check-summary.json').read_text())
print(f'PASS: {len(members)} members, exact final source/object, two standard-only reports, '
      f'{len(before["modules"])} unchanged predecessor source/receipt records')
