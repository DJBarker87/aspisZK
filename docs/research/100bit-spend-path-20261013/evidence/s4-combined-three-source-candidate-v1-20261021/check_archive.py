#!/usr/bin/env python3
from pathlib import Path
import csv, hashlib, json
root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
# Verify the immutable archive index, excluding the index itself.
listed = {}
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest, rel = line.split('  ', 1)
    listed[rel] = digest
actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p.name != 'SHA256SUMS'}
assert set(listed) == actual, (sorted(set(listed)-actual), sorted(actual-set(listed)))
for rel, digest in listed.items():
    assert sha(root/rel) == digest, rel
for p in root.rglob('*'):
    if p.is_file():
        assert p.suffix.lower() not in {'.so','.elf','.olean','.ir','.rlib','.a','.o','.pyc'}, p
pins = json.loads((root/'source-pins.json').read_text())
for rel, digest in pins['candidate_sources'].items():
    assert sha(root/'candidate-source'/Path(rel).name) == digest, rel
assert sha(root/'candidate.patch') == pins['patch_sha256']
assert sha(root/'build/receipt.json') == pins['build_receipt_sha256']
gate = json.loads((root/'six-fixture/gate-result.json').read_text())
assert gate['candidate_artifact_sha256'] == pins['candidate_elf_sha256']
assert gate['all_six_outputs_match'] is True and gate['item1_all_six_pass'] is False
rows = list(csv.DictReader((root/'six-fixture/b1-table.csv').open()))
assert len(rows) == 6 and all(r['b1_item1_pass'] == 'False' for r in rows)
standing = json.loads((root/'standing-result.json').read_text())
assert len(standing['rows']) == 30 and standing['all_exit_zero'] is True
assert all(r['exit_status'] == 0 for r in standing['rows'])
assert all(r['candidate_artifact_sha256'] == pins['candidate_elf_sha256'] for r in standing['rows'])
print(f'PASS: {len(listed)} archive files hash-checked; no binary artifacts; six B1 failures and 30 passing standing receipts verified')
