#!/usr/bin/env python3
"""Fail-closed L186 source identity preflight; stops at first evidence mismatch.

The seed is S2W's actual extraction receipt, not a newly assigned source pin.
A mismatch exits 1 and forbids claiming the later full inventory/build gate.
No Rust, Kani, Lean, build-host command, or release artifact is executed.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check():
    manifest = json.loads((HERE / 'Low_preflight_manifest.json').read_text())
    rows = []
    errors = []
    for item in manifest['receipts']:
        receipt = ROOT / item['path']
        if sha(receipt) != item['sha256']:
            errors.append({'receipt': item['path'], 'error': 'evidence hash changed'})
            continue
        data = json.loads(receipt.read_text())
        for raw_path, expected in data['source_hashes'].items():
            # The extraction workspace placed repository contents under src/.
            if not raw_path.startswith('src/'):
                raise ValueError('Unrecognized extraction path: ' + raw_path)
            path = raw_path.removeprefix('src/')
            if path.startswith('/') or '..' in Path(path).parts:
                raise ValueError('Unsafe source path: ' + path)
            current = ROOT / path
            actual = sha(current) if current.is_file() else None
            rows.append({'receipt': item['path'],
                         'json_pointer': '/source_hashes/' + raw_path.replace('/', '~1'),
                         'source': path, 'expected_sha256': expected,
                         'current_sha256': actual,
                         'current_bytes': current.stat().st_size if current.is_file() else None,
                         'status': 'match' if expected == actual else 'mismatch'})
        # Completion rule: stop the audit on a mismatch, retaining the full first receipt.
        if any(row['status'] == 'mismatch' for row in rows):
            break
    mismatch = any(row['status'] == 'mismatch' for row in rows)
    result = {'schema': 1, 'row': 'L186',
              'source_revision': manifest['source_revision'],
              'audit_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'status': 'mismatch' if mismatch else ('error' if errors else 'seed_matches_only'),
              'complete_source_to_elf_link': False,
              'scope': 'First S2W extraction receipt; remaining certificate inventory not reached under stop-on-mismatch rule.',
              'checks': rows, 'errors': errors,
              'not_run': ['full source-pin inventory', 'SBF rebuild', 'S10 ordering replay'],
              'budget_used': {'sbf': 0, 'kani': 0, 'lean': 0},
              'print_axioms': 'N/A: no Lean theorem or invocation'}
    print(json.dumps(result, indent=2))
    return 1 if mismatch or errors else 2  # Seed identity alone never closes L186.


if __name__ == '__main__':
    sys.exit(check())
