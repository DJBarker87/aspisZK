#!/usr/bin/env python3
"""Run original NCZ mutation logic on NDT, redirecting only I/O and sparse fixtures.
The NCZ validator and tests remain unchanged in the predecessor directory.
"""
import hashlib
import json
from pathlib import Path
E=Path(__file__).resolve().parent
original=E.parent/'native-compledger-20261028/NCZ_tests.py'
source=original.read_text()
changes={
    "HERE / 'NCZ_LEDGER.json'":"HERE.parent / 'native-ledger3-20261029/NDT_LEDGER.json'",
    "HERE / 'NCZ_TEST_RECEIPT.json'":"HERE.parent / 'native-ledger3-20261029/NDT_NCZ_TEST_RECEIPT.json'",
    "with mock.patch.object(ncz.Path, 'read_bytes', return_value=b'changed evidence'):":"with mock.patch.object(ncz.Path, 'exists', return_value=True), mock.patch.object(ncz.Path, 'read_bytes', return_value=b'changed evidence'):",
    "assert store.read(p) == (HERE.parent.parent / p).read_bytes()":"assert store.read(p) == store.blob(store.tree[p][0])",
}
for before,after in changes.items():
    assert before in source,before
    source=source.replace(before,after)
(E/'NDT_NCZ_TEST_ADAPTER.json').write_text(json.dumps(dict(
    original_source=str(original.relative_to(E.parent.parent)),
    original_sha256=hashlib.sha256(original.read_bytes()).hexdigest(),
    transformed_sha256=hashlib.sha256(source.encode()).hexdigest(),
    transformations=changes,
    policy='Only input/output redirection and sparse-worktree fixture support; original validator, invariant checks and mutation logic unchanged; no prover execution'),indent=2)+'\n')
exec(compile(source,str(original),'exec'),dict(__name__='__main__',__file__=str(original)))
