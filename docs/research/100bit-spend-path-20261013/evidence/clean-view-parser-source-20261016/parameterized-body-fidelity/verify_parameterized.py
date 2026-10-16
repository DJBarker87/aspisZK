#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys

root = Path('/tmp/r1-view-parse-echeck-cut-20261016/attempt-h-owned-offset-shape/output/generated/AspisR1ViewParseProbe')
outdir = Path(__file__).resolve().parent
src = root / 'Funs.lean'
out = outdir / 'ParameterizedParse.lean'
manifest = json.loads((outdir / 'manifest.json').read_text())
s = src.read_text()
start = s.index('def verifier.View.parse\n')
end = s.index('\n/-- [aspis_r1_view_parse_probe::verifier::view_parse_probe]', start)
block = s[start:end]
assert block.count('verifier.query_checks') == 4
expected = block.replace(
    'def verifier.View.parse\n',
    'def verifier.View.parse_with_query_checks\n  (query_checks : Slice Std.U8 → transport.Variant → Result (core.result.Result Unit verifier.Error))\n',
    1,
).replace('verifier.query_checks ', 'query_checks ')
assert expected.count('query_checks ') == 5  # one binder plus four applications
assert 'verifier.query_checks' not in expected
content = (
    '-- Mechanically extracted from pinned H generated Funs.lean.\n'
    '-- Exact semantic adaptation: replace external query_checks calls with one\n'
    '-- explicit function parameter; all other parse body tokens are retained.\n'
    'import AspisR1ViewParseProbe.Funs\n'
    'open Aeneas Aeneas.Std Result ControlFlow Error\n'
    'set_option autoImplicit false\n'
    'namespace AspisR1ViewParseProbe\n'
    + expected.replace('def verifier.View.parse_with_query_checks\n', 'noncomputable def verifier.View.parse_with_query_checks\n', 1) + '\nend AspisR1ViewParseProbe\n'
)
assert out.read_text() == content, 'parameterized source differs from deterministic extraction'
for path, key in [(src, 'source_funs_sha256'), (out, 'output_sha256')]:
    assert hashlib.sha256(path.read_bytes()).hexdigest() == manifest[key], f'hash mismatch: {path}'
assert hashlib.sha256(block.encode()).hexdigest() == manifest['source_function_sha256']
print('parameterized parse source verified')
print('Funs source SHA256:', manifest['source_funs_sha256'])
print('parse body SHA256:', manifest['source_function_sha256'])
print('parameterized output SHA256:', manifest['output_sha256'])
