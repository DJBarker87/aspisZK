#!/usr/bin/env python3
"""Complete-body checker for the frozen original Rev::fold polynomial port.

This checker validates source/declaration shape and the exact typed adapter
mapping.  The accompanying Lean theorem proves the operational Aeneas-loop
adapter equals the existing current-Wide unrolled body for every Result.
It does not claim that Rust std's Rev::fold is refined by the selected Aeneas
body; that is the one remaining library correspondence boundary.
"""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT if (ROOT / "input/lib.rs").exists() else ROOT.parent
INPUT = BASE / "input"
GENERATED = BASE / "generated/AspisR1FinishRelationCurrent"
LEAN = ROOT / "AeneasOriginalPolynomialBodyAdapterV1.lean"
if not LEAN.exists():
    LEAN = ROOT / "source/AeneasOriginalPolynomialBodyAdapterV1.lean"
MODEL = BASE / "AeneasCurrentWidePolynomialFoldConsumerV1.lean"
TRACE = BASE / "AeneasActualRevFoldRefinementV2.lean"
RUST = INPUT / "lib.rs"
FRAGMENT = INPUT / "fragments/polynomial.rs"
FUNS = GENERATED / "Funs.lean"
TYPES = GENERATED / "Types.lean"
PINS = BASE / "aeneas-a-evidence/input-snapshot/source-pins.json"
FROZEN_VERIFIER = ROOT / "pins/frozen-verifier-c8.rs"
if not FROZEN_VERIFIER.exists():
    FROZEN_VERIFIER = BASE.parents[1] / "evidence/session-b-fibre-point-extraction-20261019/extraction/input/source-pins/verifier.rs"

sha = lambda b: hashlib.sha256(b).hexdigest()
norm = lambda s: re.sub(r"\s+", "", s)

def need(ok: bool, why: str) -> None:
    if not ok:
        raise SystemExit("FAIL: " + why)

rust = RUST.read_bytes()
frag = FRAGMENT.read_bytes()
rust_start = rust.index(b"pub fn polynomial")
rust_end = rust.index(b"\n", rust_start)
rust_body = rust[rust_start:rust_end]
need(rust_body == frag, "frozen original Rust function differs from its pinned fragment")
need(sha(rust_body) == "ca19094cb9ea4f1b293554b0ec68d055ccc1dd71488f16f6e5f5043c631e48a7",
     "original Rust function span hash changed")
frozen_verifier = FROZEN_VERIFIER.read_bytes()
need(sha(frozen_verifier) == "8a704eea668d04ca173290ca894c7cb0ab1f29abef4fec9bb49fbb36476779ea",
     "frozen adopted verifier source hash changed")
frozen_body = frozen_verifier[12595:12695]
need(sha(frozen_body) == "ca19094cb9ea4f1b293554b0ec68d055ccc1dd71488f16f6e5f5043c631e48a7" and
     frozen_body == rust_body,
     "extraction-kit function does not match exact frozen verifier span [12595,12695)")
need(b"(0..7).rev().fold(E::ZERO,|a,i|a.mul(x).add(field(bytes,i)))" in rust_body,
     "original source is no longer the expected rev-fold expression")

funs = FUNS.read_text()
start = funs.index("def verifier.polynomial\n")
end = funs.index("\nend AspisR1VerifierPolynomialCurrent", start)
decl = funs[start:end]
need("Source: 'lib.rs', lines 862:0-862:100" in funs[start - 120:start],
     "generated declaration source span changed")
need("(bytes : Slice Std.U8) (x : aspis_core.field.WideExact)" in decl and
     "Result aspis_core.field.WideExact" in decl,
     "generated original polynomial signature changed")
need(norm("""do
  let r ← core.iter.traits.iterator.Iterator.rev.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) { start := 0#usize, «end» := 7#usize }
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
    verifier.polynomial.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
    r aspis_core.field.WideExact.ZERO (x, bytes)""") in norm(decl),
     "complete generated function body differs from pinned original fold body")

# Pin and check the entire generated callback declaration: closure environment
# (x, bytes), accumulator/index input, mul -> field -> add order, unchanged
# closure environment on return.
cbstart = funs.index("def\n  verifier.polynomial.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut")
cbend = funs.index("\n/--", cbstart)
callback = funs[cbstart:cbend]
need("let (we, s) := c" in callback and "let (a, i) := tupled_args" in callback,
     "callback parameter destructuring changed")
need(callback.index("WideExact.mul a we") < callback.index("weights.field s i") <
     callback.index("WideExact.add we1 we2") < callback.index("ok (we3, c)"),
     "callback operation/order/carry changed")

# The adapter is checked as a whole expression: concrete Aeneas loop, exact
# initial range/fuel, captured inputs, actual typed current callback, and ZERO.
lean = LEAN.read_text()
adapter = re.search(r"def originalEmittedPolynomialBody .*?:=\n(.*?)\n\n/--", lean, re.S)
need(adapter is not None, "operational adapter declaration not found")
adapter_expr = adapter.group(1)
need(norm(adapter_expr) == norm("""AspisR1CurrentWide.RevFoldRefinementV2.actualRfoldLoop 8
    AspisR1CurrentWide.RevFoldRefinementV2.actualInitialRevRange
    (AspisR1CurrentWide.AeneasPolynomialConsumer.currentPolynomialStep bytes x)
    currentWideZero"""), "adapter does not preserve whole fold operands/state")
need("actual_loop_eq_current_unrolled bytes x" in lean and
     "originalEmittedPolynomialBody_success_iff_unrolled" in lean,
     "all-outcome Lean theorem bridge missing")
need("import AspisR1VerifierPolynomialCurrent.Funs" not in lean and
     "FunsExternal" not in lean and "TypesExternal" not in lean,
     "adapter imports generated stubs/external templates")
trace_text = TRACE.read_text()
need("actualRfoldLoop_eq_foldIndices" in trace_text and
     "actual_rev_next_trace_zero_seven" in trace_text,
     "pinned operational Rev.next/Range.next_back refinement missing")
model_text = MODEL.read_text()
need("current_unrolled_record_polynomial" in model_text and
     "currentPolynomialStep" in model_text,
     "current step/unrolled consumer missing")
step_start = model_text.index("def currentPolynomialStep")
step_end = model_text.index("\ntheorem actual_loop_eq_reverseRangeResult_seven", step_start)
step = model_text[step_start:step_end]
need(norm(step[step.index(":= do") + len(":= do"):]) == norm("""
  let product ← field.wide_exact.WideExact.mul state x
  let coefficient ← currentRecordFieldLookupNat bytes index
  field.wide_exact.WideExact.add product coefficient"""),
     "operational callback does not implement the generated callback's full dataflow")

out = {
  "classification": "complete source/declaration adapter check + all-Result Lean equality; Rust std Rev::fold to Aeneas actual Rev::next loop remains explicit",
  "rust_function": {"sha256": sha(rust_body), "extraction_input_span": [rust_start, rust_end], "frozen_verifier_span": [12595, 12695], "frozen_verifier_sha256": sha(frozen_verifier), "sha256": sha(rust_body), "text": rust_body.decode()},
  "full_generated_funs_sha256": sha(FUNS.read_bytes()),
  "full_generated_types_sha256": sha(TYPES.read_bytes()),
  "generated_function": "AspisR1VerifierPolynomialCurrent.verifier.polynomial",
  "generated_body_sha256": sha(decl.encode()),
  "generated_callback_sha256": sha(callback.encode()),
  "whole_body_mapping": {
    "Range(0,7).rev() construction": "actualInitialRevRange",
    "Rev.fold DoubleEndedIterator/FnMut invocation": "actualRfoldLoop 8 actualInitialRevRange",
    "fold accumulator": "WideExact.ZERO -> currentWideZero",
    "fold closure environment": "(x, bytes), fixed across loop; callback accumulator is current state",
    "callback order": ["generated mul a we -> current mul state x", "weights.field s i -> currentRecordFieldLookupNat bytes index", "generated add we1 we2 -> current WideExact.add product coefficient"],
    "callback return": "generated (we3,c) with unchanged closure state -> updated accumulator; closure environment remains (x,bytes)",
    "usize index": "Aeneas actualRevNext index.val -> Nat passed to current parser adapter",
  },
  "lean_adapter_sha256": sha(LEAN.read_bytes()),
  "lean_adapter_theorem": "originalEmittedPolynomialBody_eq_unrolled; success iff unrolled, for all bytes/x/results",
  "current_step_source_sha256": sha(MODEL.read_bytes()),
  "current_step_declaration_sha256": sha(step.encode()),
  "actual_rev_loop_source_sha256": sha(TRACE.read_bytes()),
  "rust_source_file_sha256": sha(rust),
  "source_pins_file_sha256": sha(PINS.read_bytes()),
  "unproved_boundary": "Rust core iter Rev::fold/Range reverse iteration correspondence to emitted Aeneas Rev.next loop; generated arithmetic/field stubs excluded and replaced by checked current operations/parser adapter",
}
print(json.dumps(out, indent=2))
