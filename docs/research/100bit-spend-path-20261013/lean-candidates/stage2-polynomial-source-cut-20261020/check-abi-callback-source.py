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
CALLBACK_CONSUMER = ROOT / "abi-map-evidence-v1/unrolled-consumer/CurrentWideActualRecordFieldCallbackV1.lean"
ABI_MAP = ROOT / "CurrentWidePolynomialABIMapV1.lean"
UNROLLED = ROOT / "abi-map-evidence-v1/unrolled-consumer/CurrentWideUnrolledRecordPolynomialV1.lean"
RANGE_MODEL = ROOT / "CurrentWideReverseRangeFoldModelV1.lean"

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit("FAIL: " + message)

lib, fragment = RAW_LIB.read_text(), RAW_FRAGMENT.read_text()
types, funs = GEN_TYPES.read_text(), GEN_FUNS.read_text()
callback, abi = CALLBACK.read_text(), ABI_MAP.read_text()
callback_consumer = CALLBACK_CONSUMER.read_text()
unrolled = UNROLLED.read_text()
range_model = RANGE_MODEL.read_text()

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
callback_do = cb_body[cb_body.index(":= do") + len(":= do"):].strip()
callback_shape = """\n  let product ← field.wide_exact.WideExact.mul args.1 state.1
  let coefficient ← lookup state.2 args.2
  let next ← field.wide_exact.WideExact.add product coefficient
  ok (next, state)"""
require(normalize(callback_do) == normalize(callback_shape),
        "full callback operand/binding/return shape changed")
actual_cb_start = callback_consumer.index("theorem current_polynomial_call_mut_actual_record_field_success")
actual_cb_end = callback_consumer.index("\n#print axioms current_polynomial_call_mut_actual_record_field_success", actual_cb_start)
actual_cb = callback_consumer[actual_cb_start:actual_cb_end]
require("current_polynomial_call_mut currentRecordFieldLookup state args" in actual_cb and
        "currentRecordFieldLookup_success_canonical" in actual_cb,
        "actual record-field consumer no longer instantiates callback with concrete parser")

# The complete current-E consumer peels the actual seven-bind port on success.
u_start = unrolled.index("def current_unrolled_record_polynomial")
u_end = unrolled.index("\nprivate theorem bind_ok_inv", u_start)
u_body = unrolled[u_start:u_end]
u_ops = re.findall(r"field\.wide_exact\.WideExact\.(mul|add)|currentRecordFieldLookupNat bytes (\d+)", u_body)
u_sequence = [op if op else "field" + index for op, index in u_ops]
g_ops = re.findall(r"WideExact\.(mul|add)|weights\.field bytes (\d+)#usize", gen_poly)
g_sequence = [op if op else "field" + index for op, index in g_ops]
require(u_sequence == g_sequence, "generated and current-E seven-bind primitive sequences differ")
# Check each callback instance's whole dataflow: prior accumulator/challenge,
# returned product, parser input/index, coefficient, and next accumulator.
u_steps = u_body[u_body.index(":= do") + len(":= do"):]
lines = [line.strip() for line in u_steps.splitlines() if line.strip()]
triples = []
pos = 0
acc = "currentWideZero"
for i in range(6, -1, -1):
    mm = re.fullmatch(r"let (\w+) ← field\.wide_exact\.WideExact\.mul (\w+) x", lines[pos])
    fm = re.fullmatch(r"let (\w+) ← currentRecordFieldLookupNat bytes (\d+)", lines[pos + 1])
    require(mm is not None and fm is not None, f"callback instance {i}: mul/lookup statement shape changed")
    product, mul_acc = mm.groups()
    coefficient, index = fm.groups()
    require(mul_acc == acc and index == str(i), f"callback instance {i}: accumulator or index argument changed")
    if i != 0:
        am = re.fullmatch(r"let (\w+) ← field\.wide_exact\.WideExact\.add (\w+) (\w+)", lines[pos + 2])
        require(am is not None, f"callback instance {i}: output binding missing")
        nxt, add_product, add_coefficient = am.groups()
        pos += 3
    else:
        am = re.fullmatch(r"field\.wide_exact\.WideExact\.add (\w+) (\w+)", lines[pos + 2])
        require(am is not None, "final callback instance: returned add expression changed")
        nxt = "<returned>"
        add_product, add_coefficient = am.groups()
        pos += 3
    require(add_product == product and add_coefficient == coefficient,
            f"callback instance {i}: product/coefficient dataflow changed")
    triples.append({"index": i, "accumulator": mul_acc, "challenge": "x", "product": product,
                    "bytes": "bytes", "coefficient_index": int(index), "coefficient": coefficient,
                    "next_accumulator": nxt})
    if i != 0:
        acc = nxt
require(pos == len(lines), "unexpected extra statements after the seven callback instances")
# Compare the entire do-expression after the explicitly enumerated typed-callee
# substitutions. This checks every operand, binder, and final return expression,
# not only call counts or operation names.
generated_do = gen_poly[gen_poly.index(":= do") + len(":= do"):].strip()
current_do = u_body[u_body.index(":= do") + len(":= do"):].strip()
mapped_generated_do = generated_do
mapped_generated_do = mapped_generated_do.replace(
    "aspis_core.field.WideExact.mul", "field.wide_exact.WideExact.mul")
mapped_generated_do = mapped_generated_do.replace(
    "aspis_core.field.WideExact.add", "field.wide_exact.WideExact.add")
mapped_generated_do = mapped_generated_do.replace(
    "aspis_core.field.WideExact.ZERO", "currentWideZero")
mapped_generated_do = re.sub(
    r"weights\.field bytes (\d+)#usize",
    r"currentRecordFieldLookupNat bytes \1", mapped_generated_do)
require(normalize(mapped_generated_do) == normalize(current_do),
        "full generated/current do-expression mismatch after enumerated substitutions")
require("import AspisR1VerifierPolynomialCurrent.Funs" not in unrolled and
        "FunsExternal" not in unrolled,
        "current-E proof accidentally imports generated stubs/external templates")
require("theorem current_unrolled_record_polynomial_success" in unrolled and
        unrolled.count("rcases bind_ok_inv") == 20,
        "current-E consumer does not invert the complete seven-bind success path")
require("def reverseRangeResult" in range_model and
        "reverseRangeResult_seven" in range_model and
        "current_unrolled_eq_reverseRangeResult_seven" in range_model and
        "current_unrolled_success_iff_reverseRange_success" in range_model and
        "#print axioms current_unrolled_success_iff_reverseRange_success" in range_model,
        "formal bounded reverse-range model/actual-success bridge is absent")

# All artifacts are explicitly pinned so later edits cannot silently reuse this result.
pins = {
    "candidate_lib_sha256": sha(CAND / "input/lib.rs"),
    "candidate_function_fragment_sha256": sha(RAW_FRAGMENT),
    "candidate_integrated_function_sha256": hashlib.sha256(integrated.group(0).encode()).hexdigest(),
    "generated_types_sha256": sha(GEN_TYPES),
    "generated_funs_sha256": sha(GEN_FUNS),
    "typed_callback_sha256": sha(CALLBACK),
    "typed_callback_consumer_sha256": sha(CALLBACK_CONSUMER),
    "abi_map_sha256": sha(ABI_MAP),
    "seven_bind_consumer_sha256": sha(UNROLLED),
    "seven_bind_consumer_object_sha256": "f085072be74e80d5f3cbd913fa1476a2f0cd98e8f8eaaa17d55cf5c60472b2ec",
    "reverse_range_model_sha256": sha(RANGE_MODEL),
    "reverse_range_model_object_sha256": "91f92bec18871fc10126fee10aa21b5ead86f41eaba6688caa6134dfea373eec",
}
out = {
    "classification": "mechanical source/type/callee-order checker only; no Rust std loop-equivalence theorem",
    "checks": type_checks,
    "candidate_source_indices": src_calls,
    "generated_indices": generated_indices,
    "generated_arithmetic_sequence": generated_ops,
    "typed_current_callback_arithmetic_sequence": cb_ops,
    "typed_current_callback_lookup": "after mul and before add",
    "full_typed_callback_operands_and_return_match": True,
    "callback_parameter_mapping": {
        "generated accumulator": "args.1",
        "generated challenge x": "state.1",
        "generated bytes": "state.2",
        "generated coefficient index": "args.2",
        "generated product": "product",
        "generated fetched field": "coefficient",
        "generated returned accumulator": "next",
        "generated callback state passthrough": "state",
        "concrete parser consumer": "currentRecordFieldLookup via current_polynomial_call_mut_actual_record_field_success",
    },
    "seven_callback_dataflow_instances": triples,
    "formal_reverse_range_bridge": "current_unrolled_success_iff_boundedRange_success; source-shaped `[lo, hi)` back-step model returns `hi-1` and recurses on the shorter range; not a theorem about Rust std",
    "generated_to_current_consumer_sequence": u_sequence,
    "full_generated_body_operand_and_return_match": True,
    "enumerated_body_substitutions": {
        "generated WideExact.mul": "current field.wide_exact.WideExact.mul",
        "generated WideExact.add": "current field.wide_exact.WideExact.add",
        "generated WideExact.ZERO": "currentWideZero",
        "generated weights.field bytes N#usize": "actual currentRecordFieldLookupNat bytes N",
        "preserved": ["all do-bind order", "all intermediate variable names", "all operands", "indices", "final returned add expression"],
    },
    "current_consumer_success_theorem": "current_unrolled_record_polynomial_success; inverts seven triples and returns canonical coefficients plus decoded Horner result",
    "abi_boundary": "generated PolyWide → FinishWide → current E, with all nested coordinates proved equal by poly_wide_current_coordinates",
    "pinned_hashes": pins,
    "open": [
        "the candidate Rust explicit sequence is not yet proved equivalent to the original Range<usize>.rev().fold; the Lean model formalizes its index order and proves the current-E seven-bind success equivalence",
        "generated WideExact.mul/add fail-panic stubs and weights.field external template are excluded",
        "full caller reachability and source adoption remain open",
    ],
}
(ROOT / "abi-callback-source-check-v1.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
