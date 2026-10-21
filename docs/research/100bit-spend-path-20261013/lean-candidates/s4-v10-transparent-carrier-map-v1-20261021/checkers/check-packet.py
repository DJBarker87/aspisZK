#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'manifest.json').read_text())
def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()
checks = [
 ('sources/S4V10CarrierMapV1.lean', 'f92640dd92fa022893fb17ee3fec3db2f7650dcf2ccacacf5a916b84f2516af7'),
 ('dependencies/AspisR1FastDotsMinimalFixedCallsV10/Types.lean', 'ff5c9ce80caf212f56f241f73cab9452f380563cb83bb7ce18df0c75a71b173d'),
 ('dependencies/AspisR1FastDotsMinimalFixedCallsV10/TypesExternal.lean', 'fbc518551772a67aa3a43ef2fa54389f8b8f60bc58b444d06fb5a5c69d76d96a'),
 ('receipts/TypesExternal.log', None),
 ('receipts/Types.log', None),
 ('receipts/S4V10CarrierMapV1.log', None),
 ('commands.json', None),
 ('README.md', None),
]
for rel, want in checks:
    p = root / rel
    if not p.is_file(): raise SystemExit(f'missing {rel}')
    got = sha(p)
    if want and got != want: raise SystemExit(f'hash mismatch {rel}: {got}')
log = (root / 'receipts/S4V10CarrierMapV1.log').read_text()
for theorem in ('wideCarrierEquiv', 'wide_coordinates_preserved'):
    if theorem not in log or 'does not depend on any axioms' not in log:
        raise SystemExit(f'missing standard axiom audit for {theorem}')
external = (root / 'dependencies/AspisR1FastDotsMinimalFixedCallsV10/TypesExternal.lean').read_text()
if 'axiom ' in external or 'abbrev EbyKDot := AspisR1EbyKPushCutV3.fast_pairing.EbyKDot' not in external:
    raise SystemExit('external type adapter is not the explicit concrete carrier alias')
if any(root.rglob('FunsExternal.lean')) or any(root.rglob('*.olean')):
    raise SystemExit('packet must not contain generated FunsExternal or Lean binaries')
for entry in manifest['direct_import_source_map'].values():
    src = entry.get('source', '')
    if src.startswith('../../'):
        if not (root / src).resolve().is_file(): raise SystemExit(f'unresolved source path: {src}')
print('PASS: source hashes, receipts, explicit type adapter, standard axiom audit, source-only packet')
