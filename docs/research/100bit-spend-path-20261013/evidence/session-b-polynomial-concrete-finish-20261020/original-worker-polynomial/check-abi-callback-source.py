#!/usr/bin/env python3
"""Pinned, mechanical ABI/operation-path check for the unrolled polynomial candidate.

This checks source/declaration shape and source pins; it is not a semantic theorem
for Rust std Rev::fold or for the emitted fail/panic external arithmetic stubs.
"""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CAND = ROOT / "unrolled-candidate-v1"
GEN = CAND / "generated/AspisR1FinishRelationCurrent"
RAW_LIB = CAND / "input/lib.rs"
RAW_FRAGMENT = CAND / "input/fragments/polynomial.rs"
GEN_TYPES = GEN / "Types.lean"
GEN_FUNS = GEN / "Funs.lean"
CALLBACK = ROOT / "CurrentWidePolynomialCallback.lean"
ABI_MAP = ROOT / "CurrentWidePolynomialABIMapV1.lean"
UNROLLED = ROOT / "abi-map-evidence-v1/unrolled-consumer/CurrentWideUnrolledRecordPolynomialV1.lean"

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit("FAIL: " + message)

lib, fragment = RAW_LIB.read_text(), RAW_FRAGMENT.read_text()
types, funs = GEN_TYPES.read_text(), GEN_FUNS.read_text()
callback, abi = CALLBACK.read_text(), ABI_MAP.read_text()
unrolled = UNROLLED.read_text()

# Exact generated candidate nominal type structure and its current-coordinate proof.
type_checks = {
    "generated M31 alias": "def aspis_core.field.M31 := Std.U32" in types,
    "generated CM31 field order": bool(re.search(r"structure aspis_core\.field\.CM31 where\s+a : aspis_core\.field\.M31\s+b : aspis_core\.field\.M31", types)),
    "generated QM31 field order": bool(re.search(r"structure aspis_core\.field\.QM31 where\s+c0 : aspis_core\.field\.CM31\s+c1 : aspis_core\.field\.CM31", types)),
    "generated WideExact field order": bool(re.search(r"structure aspis_core\.field\.WideExact where\s+c0 : aspis_core\.field\.QM31\s+c1 : aspis_core\.field\.QM31", types)),
    "formal generated-to-current coordinate theorem": "theorem poly_wide_current_coordinates" in abi,
    "conversion explicitly passes through FinishE": "ofFinishE (polyWideToFinish x)" in abi,
    "generated arithmetic stubs excluded from callback": "AspisR1VerifierPolynomialCurrent.aspis_core.field.WideExact.mul" not in callback and "AspisR1VerifierPolynomialCurrent.aspis_core.field.WideExact.add" not in callback,
}
require(all(type_checks.values()), "generated/current ABI check failed: " + repr(type_checks))

# The replacement Rust cut contains exactly seven source calls, index 6 down to 0.
src_calls = re.findall(r"\.mul\(x\)\.add\(field\(bytes,(\d+)\)\)", fragment)
require(src_calls == [str(i) for i in range(6, -1, -1)], "Rust candidate expression sequence differs")
integrated = re.search(r"pub fn polynomial\([^\n]*\)\s*->\s*E\s*\{.*?\n\}", lib, re.S)
require(integrated is not None, "candidate function not found in integrated lib.rs")
normalize = lambda s: re.sub(r"\s+", "", s)
require(normalize(integrated.group(0)) == normalize(fragment),
        "candidate integrated lib.rs body differs from frozen polynomial fragment")

# Extract only the generated verifier.polynomial declaration and inspect the sequence.
start = funs.index("def verifier.polynomial")
end = funs.index("\nend AspisR1VerifierPolynomialCurrent", start)
gen_poly = funs[start:end]
generated_indices = re.findall(r"weights\.field bytes (\d+)#usize", gen_poly)
generated_ops = re.findall(r"WideExact\.(mul|add)", gen_poly)
require(generated_indices == [str(i) for i in range(6, -1, -1)], "generated field read sequence differs")
require(generated_ops == [op for _ in range(7) for op in ("mul", "add")], "generated mul/add sequence differs")
require("(bytes : Slice Std.U8) (x : aspis_core.field.WideExact)" in gen_poly and "Result aspis_core.field.WideExact" in gen_poly,
        "generated function ABI changed")

# The reusable current-E callback implements precisely the per-index triple.
cb_start = callback.index("def current_polynomial_call_mut")
cb_end = callback.index("\ntheorem current_polynomial_call_mut_success", cb_start)
cb_body = callback[cb_start:cb_end]
cb_ops = re.findall(r"field\.wide_exact\.WideExact\.(mul|add)", cb_body)
require(cb_ops == ["mul", "add"], "typed current callback arithmetic order differs")
require("let coefficient ← lookup state.2 args.2" in cb_body, "typed current callback lookup position differs")
require("let product ← field.wide_exact.WideExact.mul args.1 state.1" in cb_body,
        "typed current callback multiplicand order differs")
require("let next ← field.wide_exact.WideExact.add product coefficient" in cb_body,
        "typed current callback addition order differs")

# The complete current-E consumer peels the actual seven-bind port on success.
u_start = unrolled.index("def current_unrolled_record_polynomial")
u_end = unrolled.index("\nprivate theorem bind_ok_inv", u_start)
u_body = unrolled[u_start:u_end]
u_ops = re.findall(r"field\.wide_exact\.WideExact\.(mul|add)|currentRecordFieldLookupNat bytes (\d+)", u_body)
u_sequence = [op if op else "field" + index for op, index in u_ops]
g_ops = re.findall(r"WideExact\.(mul|add)|weights\.field bytes (\d+)#usize", gen_poly)
g_sequence = [op if op else "field" + index for op, index in g_ops]
require(u_sequence == g_sequence, "generated and current-E seven-bind primitive sequences differ")
require("import AspisR1VerifierPolynomialCurrent.Funs" not in unrolled and
        "FunsExternal" not in unrolled,
        "current-E proof accidentally imports generated stubs/external templates")
require("theorem current_unrolled_record_polynomial_success" in unrolled and
        unrolled.count("rcases bind_ok_inv") == 20,
        "current-E consumer does not invert the complete seven-bind success path")

# All artifacts are explicitly pinned so later edits cannot silently reuse this result.
pins = {
    "candidate_lib_sha256": sha(CAND / "input/lib.rs"),
    "candidate_function_fragment_sha256": sha(RAW_FRAGMENT),
    "candidate_integrated_function_sha256": hashlib.sha256(integrated.group(0).encode()).hexdigest(),
    "generated_types_sha256": sha(GEN_TYPES),
    "generated_funs_sha256": sha(GEN_FUNS),
    "typed_callback_sha256": sha(CALLBACK),
    "abi_map_sha256": sha(ABI_MAP),
    "seven_bind_consumer_sha256": sha(UNROLLED),
    "seven_bind_consumer_object_sha256": "f085072be74e80d5f3cbd913fa1476a2f0cd98e8f8eaaa17d55cf5c60472b2ec",
}
out = {
    "classification": "mechanical source/type/callee-order checker only; no Rust std loop-equivalence theorem",
    "checks": type_checks,
    "candidate_source_indices": src_calls,
    "generated_indices": generated_indices,
    "generated_arithmetic_sequence": generated_ops,
    "typed_current_callback_arithmetic_sequence": cb_ops,
    "typed_current_callback_lookup": "after mul and before add",
    "generated_to_current_consumer_sequence": u_sequence,
    "current_consumer_success_theorem": "current_unrolled_record_polynomial_success; inverts seven triples and returns canonical coefficients plus decoded Horner result",
    "abi_boundary": "generated PolyWide → FinishWide → current E, with all nested coordinates proved equal by poly_wide_current_coordinates",
    "pinned_hashes": pins,
    "open": [
        "the candidate Rust explicit sequence is not yet proved equivalent to the original Range<usize>.rev().fold",
        "generated WideExact.mul/add fail-panic stubs and weights.field external template are excluded",
        "full caller reachability and source adoption remain open",
    ],
}
(ROOT / "abi-callback-source-check-v1.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
