#!/usr/bin/env python3
"""Verify v34's emittedRaw body is the pinned generated body modulo listed callee adapters."""
from pathlib import Path
import hashlib
import sys

raw_path = Path(sys.argv[1])
candidate_path = Path(sys.argv[2])
raw = raw_path.read_text()
candidate = candidate_path.read_text()

def extract(text: str, declaration: str, end_marker: str) -> str:
    start_decl = text.index(declaration)
    start = text.index(':= do\n', start_decl) + len(':= do\n')
    end = text.index(end_marker, start)
    return text[start:end]

raw_body = extract(raw, 'def verifier.query_values_entry', '\nend AspisR1QueryGeometryActual')
candidate_body = extract(candidate, 'def emittedRawWithCallees', '\n\ndef directWithCallees')
replacements = [
    ('domain.FibreIndex.new', 'R17QueryValuesEntryActualV1.fibreIndexNew', 3),
    ('fast_domain.fibre_point', 'cs.fibrePoint', 1),
    ('fast_domain.line_node', 'cs.lineNode', 2),
    ('field.M31.mul', 'cs.mul', 1),
    ('field.M31.double', 'cs.double', 1),
    ('field.M31.sub', 'cs.sub', 1),
    ('field.M31.ONE', 'cs.one', 1),
    ('Error.Query', 'QueryValuesError.Query', 1),
    ('FromSame\n          Error', 'FromSame\n          SourceError', 1),
    ('FromSame Error', 'FromSame SourceError', 2),
    ('verifier.query_values_entry.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError', 'sourceErrorMapFnOnce', 1),
    ('verifier.query_values_entry.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError', 'sourceErrorMapFnOnce', 1),
    ('verifier.query_values_entry.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError', 'sourceErrorMapFnOnce', 1),
    ('core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any\n            verifier.query_values_entry.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool\n            i4 ()', 'anyCheck i4', 1),
]
for old, new, expected in replacements:
    actual = raw_body.count(old)
    if actual != expected:
        raise SystemExit(f'expected {expected} occurrences of {old!r}, found {actual}')
    raw_body = raw_body.replace(old, new)
if raw_body != candidate_body:
    import difflib
    sys.stderr.writelines(difflib.unified_diff(raw_body.splitlines(True), candidate_body.splitlines(True), fromfile='transformed-raw', tofile='candidate'))
    raise SystemExit('candidate body differs beyond enumerated substitutions')
print(f'generated_source_sha256={hashlib.sha256(raw_path.read_bytes()).hexdigest()}')
print(f'adapted_source_sha256={hashlib.sha256(candidate_path.read_bytes()).hexdigest()}')
print(f'body_sha256={hashlib.sha256(candidate_body.encode()).hexdigest()}')
print(f'body_bytes={len(candidate_body)}')
print(f'enumerated_substitutions={len(replacements)}; exact_body_match=true')
