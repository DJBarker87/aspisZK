#!/usr/bin/env python3
"""Check generated original Dot.push loop definitions against the clean Lean adapter.

This is a source-body identity check, not a Rust library semantic proof. It verifies:
* generated Types are copied byte-for-byte except removal of all generated `set_option` lines;
* P, push_loop.body, and push_loop definitions are exact copied blocks;
* outer push differs only by replacing `Q.raw a b` with explicit `rawFn a b`.
"""
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def block(text: str, start: str, end: str) -> str:
    i = text.index(start)
    j = text.index(end, i + len(start))
    return text[i:j].strip()


def body(text: str, marker: str) -> str:
    i = text.index(marker)
    rest = text[i:]
    return rest.split(':= do', 1)[1].strip()

def norm(text: str) -> str:
    return re.sub(r'\s+', ' ', text).strip()

ap = argparse.ArgumentParser()
ap.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[6])
ap.add_argument('--packet-local', action='store_true')
ap.add_argument('--out', type=Path)
args = ap.parse_args()
repo = args.repo.resolve()
if args.packet_local:
    packet = Path(__file__).resolve().parents[1]
    source_types = packet / 'source/dot-push/generated/Types.lean'
    source_funs = packet / 'source/dot-push/generated/Funs.lean'
    adapted_types = packet / 'source/dot-push/adapter/AspisR1EbyKDotPushSourceV1/Types.lean'
    adapted_adapter = packet / 'source/dot-push/adapter/AspisR1EbyKDotPushSourceV1/LoopAdapter.lean'
    adapted_proof = packet / 'source/dot-push/proof/OriginalDotPushRawLoopToLiteralV1.lean'
else:
    base = repo / 'docs/research/100bit-spend-path-20261013'
    proof = base / 'lean-candidates/s5-current-repin-20261020/sources'
    evidence = base / 'evidence/s5-current-repin-20261020/original-dot-push-raw-boundary-v1'
    generated = evidence / 'generated/AspisR1EbyKDotPushSourceV1'
    source_types = generated / 'Types.lean'
    source_funs = generated / 'Funs.lean'
    adapted_types = proof / 'AspisR1EbyKDotPushSourceV1/Types.lean'
    adapted_adapter = proof / 'AspisR1EbyKDotPushSourceV1/LoopAdapter.lean'
    adapted_proof = proof / 'GeneratedOriginalDotPushLoopLiteralV1.lean'

raw_types = source_types.read_text()
expected_types = '\n'.join(x for x in raw_types.splitlines() if not x.startswith('set_option ')).strip()
actual_types = adapted_types.read_text().strip()
assert expected_types == actual_types, 'Types body changed beyond removal of set_option directives'

funs = source_funs.read_text()
adapter = adapted_adapter.read_text()
p_start = '@[global_simps, irreducible]\ndef fast_pairing.canonical.P'
body_start = '@[rust_loop_body]\ndef fast_pairing.canonical.Dot.push_loop.body'
loop_start = '@[rust_loop]\ndef fast_pairing.canonical.Dot.push_loop'
p_src = block(funs, p_start, '/-- [eby_k_push_cut::fast_pairing::canonical::{eby_k_push_cut::fast_pairing::canonical::Dot}::push]: loop body')
p_adapt = block(adapter, p_start, body_start)
body_src = block(funs, body_start, '/-- [eby_k_push_cut::fast_pairing::canonical::{eby_k_push_cut::fast_pairing::canonical::Dot}::push]: loop 0:')
body_adapt = block(adapter, body_start, loop_start)
push_src = block(funs, 'def fast_pairing.canonical.Dot.push\n', 'def fast_pairing.dot_push_entry')
push_adapt = block(adapter, 'def fast_pairing.canonical.Dot.push_raw\n', '\nend AspisR1EbyKDotPushSourceV1')
loop_src = block(funs, loop_start, '/-- [eby_k_push_cut::fast_pairing::canonical::{eby_k_push_cut::fast_pairing::canonical::Dot}::push]:\n')
loop_adapt = block(adapter, loop_start, 'def fast_pairing.canonical.Dot.push_raw\n')
assert norm(p_src) == norm(p_adapt), 'P definition differs'
assert norm(body_src) == norm(body_adapt), 'push_loop.body differs from emitted Funs'
assert norm(loop_src) == norm(loop_adapt), 'push_loop differs from emitted Funs'
source_outer = push_src.split(':= do', 1)[1].split('/--', 1)[0].strip()
adapt_outer = push_adapt.split(':= do', 1)[1].strip()
assert norm(source_outer.replace('fast_pairing.canonical.Q.raw a b', 'rawFn a b')) == norm(adapt_outer), 'outer push has changes besides Q.raw parameterization'
assert 'FunsExternal' not in adapted_adapter.read_text()
assert not any('set_option maxHeartbeats' in x or 'set_option maxRecDepth' in x for x in adapted_types.read_text().splitlines())

result = {
  'result': 'pass',
  'scope': 'generated Types/P/push_loop.body/push_loop are copied exactly; outer Dot.push differs only by explicit rawFn parameterization',
  'source_pins': {
    'original_fast_pairing_rs_sha256': '5a84d748e3ac495a664e6b476c0b91a4bfa47408e76661a2834726d40ff28ea0',
    'generated_types_sha256': sha(source_types),
    'generated_funs_sha256': sha(source_funs),
    'adapted_types_sha256': sha(adapted_types),
    'adapted_loop_adapter_sha256': sha(adapted_adapter),
    'proof_sha256': sha(adapted_proof),
  },
  'excluded': ['FunsExternal_Template.lean', 'all generated set_option directives'],
  'remaining_boundary': 'Q.raw is an explicit function argument; this checker does not prove Rust std/library semantics or the caller identity of that raw function.'
}
if args.out:
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
