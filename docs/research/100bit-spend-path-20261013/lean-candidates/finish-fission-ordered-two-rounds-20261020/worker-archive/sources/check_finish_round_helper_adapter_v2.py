#!/usr/bin/env python3
"""Mechanical full-body/order check for the V2 finish-round helper adapter.

This verifies a pinned Rust candidate and exact generated Lean body, then
normalizes only the listed callee/operator substitutions and checks equality
with the V2 adapter body. It is a source correspondence check, not a Lean
semantics proof, production reachability proof, or equivalence to the frozen
finish_relation caller.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent.parent
RUST = ROOT / 'extraction/input/lib.rs'
FUNS = ROOT / 'extraction/generated/AspisR1FinishRelationCurrent/Funs.lean'
ADAPTER = ROOT / 'sources/FinishFissionHelperAdapterV2.lean'

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def rust_fn(text: str, name: str):
    start = text.index(f'pub fn {name}(')
    brace = text.index('{', start)
    depth = 0
    for i in range(brace, len(text)):
        if text[i] == '{':
            depth += 1
        elif text[i] == '}':
            depth -= 1
            if depth == 0:
                return start, i + 1, text[start:i + 1]
    raise AssertionError(f'unterminated Rust function {name}')

def lean_body(text: str, start_marker: str, end_marker: str) -> str:
    start = text.index(start_marker)
    end = text.index(end_marker, start)
    body = text[start:end]
    return body.split(':= do', 1)[1]

rust_raw = RUST.read_bytes()
rust_text = rust_raw.decode()
rs, re_, rust_helper = rust_fn(rust_text, 'finish_relation_round')
assert sha(rust_raw) == 'a222c9f1a4da189e5123e324a6586c95d31b10cf63fb1cba61686c0a6928b6f8'
assert sha(rust_helper.encode()) == 'e664741d2208bac1355c5b53e8f367dc50c7d70e08ffc6ca4e7bf27a629ca943'

rust_compact = re.sub(r'\s+', '', rust_helper)
rust_order = [
    'select_round_poly(v,round)',
    'field(poly,0)',
    'field(poly,4)',
    'claim.mul_m31(QUARTER)',
    'crate::trace::value(15,3*round,lhs)',
    'crate::trace::value(15,3*round+1,rhs)',
    'iflhs!=rhs',
    'polynomial(poly,p.alpha[round])',
    'crate::trace::value(15,3*round+2,claim)',
    'Ok(claim)',
]
positions = [rust_compact.index(x) for x in rust_order]
assert positions == sorted(positions)
assert 'field(poly,0).add(field(poly,4))' in rust_compact
assert rust_compact.index('p.alpha[round]') > rust_compact.index('iflhs!=rhs')

funs_raw = FUNS.read_bytes()
funs = funs_raw.decode()
generated = lean_body(
    funs,
    'def verifier.finish_relation_round\n',
    '\nend AspisR1FinishRelationCurrent',
)
adapter_text = ADAPTER.read_text()
adapter = lean_body(
    adapter_text,
    'def finishRoundAdapter {W D : Type}',
    '\nprivate theorem bind_success',
)

def compact(text: str) -> str:
    return re.sub(r'\s+', '', text)

mapped = compact(generated)
adapter_compact = compact(adapter)
# Exact, enumerated source-level callee/operator substitutions. The final
# equality checks every operand, let binding, branch, return, and order.
substitutions = [
    ('verifier.select_round_poly', 'AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel'),
    ('weights.field', 'ops.field'),
    ('aspis_core.field.WideExact.add', 'ops.add'),
    ('weights.QUARTER', 'ops.quarter'),
    ('aspis_core.field.WideExact.mul_m31', 'ops.mulM31'),
    (
        'core.cmp.PartialEq.ne.trait_defaultaspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact',
        'core.cmp.PartialEq.ne.trait_default(aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExactops)',
    ),
    ('letwe2←Array.index_usizep.alpharound', 'letalpha←selectRoundAlphaModelpround'),
    ('verifier.polynomial', 'ops.polynomial'),
    ('elseletalpha←', 'elsedoletalpha←'),
    ('polywe2', 'polyalpha'),
]
for old, new in substitutions:
    assert old in mapped, f'missing expected source fragment: {old}'
    mapped = mapped.replace(old, new)
assert mapped == adapter_compact, 'complete mapped generated body differs from V2 adapter'

print(json.dumps({
    'status': 'PASS',
    'classification': 'complete-body structural correspondence after enumerated callee/operator substitutions; not an operational semantics or caller-reachability proof',
    'rust_candidate_source_sha256': sha(rust_raw),
    'rust_function_span_bytes': [rs, re_],
    'rust_function_sha256': sha(rust_helper.encode()),
    'generated_funs_sha256': sha(funs_raw),
    'generated_body_sha256': sha(generated.encode()),
    'v2_adapter_source_sha256': sha(ADAPTER.read_bytes()),
    'mapped_body_equals_adapter': True,
    'verified_order': [
        'selector', 'field[0]', 'field[4]', 'add', 'quarter', 'mul_m31',
        'trace lhs', 'trace rhs', 'comparison guard', 'alpha[round] only on non-reject branch',
        'polynomial', 'trace output', 'return claim',
    ],
    'substitutions': [
        'selected polynomial helper to selector model',
        'weights.field to FinishOps.field',
        'WideExact.add to FinishOps.add',
        'weights.QUARTER to FinishOps.quarter',
        'WideExact.mul_m31 to FinishOps.mulM31',
        'generated PartialEq instance to explicit FinishOps equality instance',
        'Array.index_usize p.alpha round to the named selectRoundAlphaModel',
        'verifier.polynomial to FinishOps.polynomial',
        'monadic else block syntax normalization',
    ],
}, indent=2))
