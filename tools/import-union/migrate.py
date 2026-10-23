#!/usr/bin/env python3
"""Deterministic discriminant migration; default scope excludes lean-candidates.

--apply writes only the attribute token and one adapter import. --check is
read-only and fails if eligible attributes remain. Explicit --candidate-root
is reserved for session A's use; it cannot select files outside lean-candidates.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

# Generated attributes start with discriminant; preserve tags, scalar and rust_type bytes.
TOKEN = re.compile(rb'(@\[)discriminant\b')
IMPORT = b'import ImportUnionNamedDiscriminant\n'

def transform(data):
    out, count = TOKEN.subn(rb'\1import_union_discriminant', data)
    if count and not re.search(rb'^import ImportUnionNamedDiscriminant\r?$', out, re.M):
        match = re.search(rb'^import [^\r\n]+\r?\n', out, re.M)
        if match is None:
            raise ValueError('generated module has no import line')
        newline = b'\r\n' if match[0].endswith(b'\r\n') else b'\n'
        out = out[:match.end()] + IMPORT.replace(b'\n', newline) + out[match.end():]
    return out, count

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2])
    ap.add_argument('--candidate-root', type=Path, action='append', default=[])
    ap.add_argument('--manifest', type=Path, required=True)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = ap.parse_args()
    repo = args.repo.resolve()
    if args.candidate_root:
        roots = [(repo / p).resolve() for p in args.candidate_root]
        if any(not r.is_relative_to(repo / 'docs/research') or 'lean-candidates' not in r.parts for r in roots):
            ap.error('candidate roots must be explicit docs/research/**/lean-candidates subdirectories')
        paths = sorted({p for r in roots for p in r.rglob('*.lean')})
    else:
        paths = sorted(p for p in (repo / 'docs/research').rglob('*.lean')
                       if 'lean' in p.relative_to(repo / 'docs/research').parts[:-1]
                       and 'lean-candidates' not in p.parts)
    records = []
    for p in paths:
        before = p.read_bytes()
        after, count = transform(before)
        if count:
            if p.is_symlink() or not p.resolve().is_relative_to(repo):
                raise ValueError('refuse migration through a source symlink: '+str(p))
            records.append({'path': p.relative_to(repo).as_posix(),
                            'before_sha256': hashlib.sha256(before).hexdigest(),
                            'after_sha256': hashlib.sha256(after).hexdigest(),
                            'attributes': count, 'before_bytes': len(before), 'after_bytes': len(after)})
            if args.apply:
                p.write_bytes(after)
    receipt = {'schema': 'import-union-migration-v1', 'mode': 'apply' if args.apply else 'check',
               'scope': [str(r.relative_to(repo)) for r in roots] if args.candidate_root else 'docs/research/**/lean/**/*.lean; excludes lean-candidates',
               'files': records, 'file_count': len(records),
               'attribute_count': sum(r['attributes'] for r in records)}
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: receipt[k] for k in ['mode', 'file_count', 'attribute_count']}))
    return int(args.check and bool(records))

if __name__ == '__main__':
    raise SystemExit(main())
