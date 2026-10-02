#!/usr/bin/env python3
"""Read-only consistency check for the saved R327 LLBC Option census."""
import hashlib
import json
from pathlib import Path

REPO = Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
OUT = Path(__file__).resolve().parent / 'R327-option-preflight.json'
INPUT = REPO / '.r21-scratch/r327-private-batch-source-try-fold/R327PrivateBatchSourceTryFold.llbc'
DECODED = REPO / '.r21-scratch/r327-private-batch-source-try-fold/source-body-audit/decoded-target-rows.json'
R331 = REPO / '.r21-scratch/r331-mono-option-return-preflight/option-return-preflight.json'
R375 = REPO / '.r21-scratch/r375-pending-return-carrier-api/R327.option-and-controlflow-rows.json'
EXPECTED = '9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

actual = sha(INPUT)
decoded = json.loads(DECODED.read_text())
r331 = json.loads(R331.read_text())
r375 = json.loads(R375.read_text())
option_rows_375 = [r for r in r375['options'] if r.get('lang_item') == 'Option']
option_rows_331 = r331['option_language_item_inventory']['rows']
assert actual == EXPECTED
assert decoded['input_sha256'] == actual
assert r331['input_llbc_sha256'] == actual
assert r375['source'].startswith('R327PrivateBatchSourceTryFold.llbc')
assert r375['option_lang_item_count'] == 3
assert r331['option_language_item_inventory']['count'] == 3
ids = [r['def_id'] for r in option_rows_331]
assert len(option_rows_375) == len(option_rows_331) == 3
assert ids == [9, 12, 13]
assert [r['def_id'] for r in option_rows_375] == ids
assert all(r['base_name'] == 'core::option::Option' and r['opacity'] == 'Transparent' for r in option_rows_331)
assert all([v['name'] for v in r['variants']] == ['None', 'Some'] for r in option_rows_331)

result = {
    'status': 'PASS: saved LLBC hash and two existing decoded Option inventories agree; no extraction or translation run',
    'input_llbc': {'path': str(INPUT.relative_to(REPO)), 'sha256': actual, 'bytes': INPUT.stat().st_size},
    'crosscheck_sources': {
        'decoded_target_rows': {'path': str(DECODED.relative_to(REPO)), 'sha256': sha(DECODED)},
        'R331_option_inventory': {'path': str(R331.relative_to(REPO)), 'sha256': sha(R331)},
        'R375_option_rows': {'path': str(R375.relative_to(REPO)), 'sha256': sha(R375)},
    },
    'option_count': 3,
    'def_ids': ids,
    'variant_names': ['None', 'Some'],
    'basis': 'The count and declaration IDs come from the existing R331/R375 decoded type inventories, cross-checked for agreement; the R327 function-body inventory is checked for matching input hash but does not enumerate type declarations. This script does not decode LLBC anew.',
    'scope': 'Mechanical source inventory only; no claim about Aeneas translation or source/model correspondence.'
}
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
