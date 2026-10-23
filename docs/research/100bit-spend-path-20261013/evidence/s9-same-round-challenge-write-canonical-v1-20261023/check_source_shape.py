#!/usr/bin/env python3
"""Pinned source-shape check: generated attempt26 body vs parameterized Lean body."""
from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
RUST = ROOT / 'source-origin/r1_semantic.rs'
GENERATED = ROOT / 'source-origin/Funs.raw-generated.lean'
MODEL = ROOT / 'sources/ActualSemanticRoundSourceOwnerLinkV1.lean'
EXPECTED = {
    RUST: 'c66eba53bc3cdf801466455089d7189c02a0bec858f407a5fc9db35d10b17013',
    GENERATED: '934f2ce717f8fd28ef7d722462fe93a5ea21f8e88207d1d6d46c40684d49b1d1',
    MODEL: '36ed9c22a452409c1efaf5c2a625c2bb71a15227611bd8786970f252d0936bce',
}

def pinned(path: Path) -> str:
    data = path.read_bytes()
    got = sha256(data).hexdigest()
    if got != EXPECTED[path]:
        raise SystemExit(f'pin mismatch: {path}: {got}')
    return data.decode()

def body(text: str, marker: str, next_marker: str) -> str:
    i = text.index(marker)
    i = text.index(':= do', i) + len(':= do')
    j = text.index(next_marker, i)
    return text[i:j]

rust = pinned(RUST)
generated = pinned(GENERATED)
model = pinned(MODEL)
# Pin the Rust function's exact span and body boundary. This does not claim Rust
# binary/MIR refinement; the generated-owner annotation carries the same span.
rust_lines = rust.splitlines()
if not any('fn semantic_round<' in line for line in rust_lines[95:111]):
    raise SystemExit('expected non-prover Rust semantic_round span not found')
if "Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 96:0-111:1" not in generated:
    raise SystemExit('generated source-span annotation changed')

a = body(generated, 'def r1_semantic.semantic_round', '\n/-- [aspis_r1_cost_probe::r1_semantic::focused_semantic_round_entry]')
m = body(model, 'def emittedRound', '\ntheorem source_model_eq_parameterized_emission')
# Replace only the four explicitly parameterized method slots and argument alias.
for old, new in [
    ('aspis_coredigestDigest32Inst', 'D'),
    ('prefix1', 'pref'),
    ('r1_wire.ValidatedRecord.decode_k 28#usize vr 0#usize', 'B.decode 28#usize vr 0#usize'),
    ('r1_semantic.semantic_boundary val', 'B.boundary val'),
    ('core.cmp.PartialEq.ne.trait_default\n          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 boundary running', 'B.neq boundary running'),
    ('r1_semantic.semantic_value val alpha1 round', 'B.value val alpha1 round'),
]:
    a = a.replace(old, new)

def normalize(text: str) -> str:
    text = text.replace('aspis_core.field.QM31', 'QM')
    text = text.replace('AspisR1ActualSemanticRoundCutV1.r1_wire.', 'r1_wire.')
    text = text.replace('(r1_wire.SemanticTranscript H)', 'r1_wire.SemanticTranscript H')
    return re.sub(r'\s+', ' ', text).strip()

if normalize(a) != normalize(m):
    raise SystemExit('normalized generated/model body mismatch')
print('PASS: pinned Rust span, generated body, and parameterized Lean body hashes match; normalized generated/model bodies equal.')
print('Scope: source-shape correspondence only; no claim about compiler binary, MIR, or runtime refinement.')
