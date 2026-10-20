#!/usr/bin/env python3
"""Create/check an exact namespace-and-import-only QRaw proof-cone rebase."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

BASE = Path('/tmp/s5-qraw-namespace-rebase-inputs')
OUT = Path(__file__).resolve().parents[1] / 'sources'
FILES = [
    'QRawSuccessTracePropV4.lean',
    'QRawNoWrapFactsV5.lean',
    'QRawPartialFoldBridgeV7.lean',
    'QRawNoWrapFromCanonicalTraceV1.lean',
    'QRawTraceUVBridgeV2.lean',
    'QRawActualCoefficientsFromBoundsV2.lean',
    'QRawGeneratedDotPushConnectionV2.lean',
    'EbyKPushActualRawCoefficientBoundsV10.lean',
    'EbyKPushDecodedProductUpdateV1.lean',
]
MODULES = {
    'QRawSuccessTracePropV4': 'S5QRaw.SuccessTracePropV4',
    'QRawNoWrapFactsV5': 'S5QRaw.NoWrapFactsV5',
    'QRawPartialFoldBridgeV7': 'S5QRaw.PartialFoldBridgeV7',
    'QRawNoWrapFromCanonicalTraceV1': 'S5QRaw.NoWrapFromCanonicalTraceV1',
    'QRawTraceUVBridgeV2': 'S5QRaw.TraceUVBridgeV2',
    'QRawActualCoefficientsFromBoundsV2': 'S5QRaw.ActualCoefficientsFromBoundsV2',
    'QRawGeneratedDotPushConnectionV2': 'S5QRaw.GeneratedDotPushConnectionV2',
    'EbyKPushActualRawCoefficientBoundsV10': 'S5QRaw.EbyKPushActualRawCoefficientBoundsV10',
    'EbyKPushDecodedProductUpdateV1': 'S5QRaw.EbyKPushDecodedProductUpdateV1',
}
REPL = [
    ('AspisR1CanonicalDotFinish.Proof', 'AspisR1CanonicalQRawUnified.Proof'),
    ('AspisR1CanonicalDotFinish', 'AspisR1CanonicalQRawUnified'),
    ('AspisR1CanonicalQRaw.Funs', 'AspisR1CanonicalQRawUnified.Funs'),
]
for old, new in MODULES.items():
    REPL.append((f'import {old}\n', f'import {new}\n'))

def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def expected(src: str) -> str:
    out = src
    for a,b in REPL:
        out = out.replace(a,b)
    return out

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    ns = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    rows = []
    bad = False
    for name in FILES:
        raw = (BASE/name).read_text()
        adapted = expected(raw)
        dest = OUT/name
        if ns.check:
            actual = dest.read_text() if dest.exists() else ''
            ok = actual == adapted
            bad |= not ok
        else:
            dest.write_text(adapted)
            ok = True
        # Reverse only the declared transformations and verify exact source recovery.
        reverse = adapted
        for a,b in reversed(REPL):
            reverse = reverse.replace(b,a)
        reverse_ok = reverse == raw
        bad |= not reverse_ok
        rows.append({
            'source': str(BASE/name), 'source_sha256': sha(raw.encode()),
            'adapted': str(dest), 'adapted_sha256': sha(adapted.encode()),
            'exact_transform_check': ok, 'reverse_recovery_check': reverse_ok,
            'module': MODULES[name.removesuffix('.lean')],
        })
    report = {'schema':'s5-qraw-namespace-rebase-v1','replacements':REPL,'modules':rows}
    (OUT.parent/'rebase-manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'ok':not bad,'modules':len(rows),'manifest':str(OUT.parent/'rebase-manifest.json')},indent=2))
    if bad: raise SystemExit(1)

if __name__ == '__main__': main()
