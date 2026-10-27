# Resume 2026-10-27

Baseline c35956a836; Env-J 43000–43299, new 100 Lean / 8 Kani budget, last three charged Lean attempts reserved for bundle audits. Prior tally retained as TALLY-prior.json. Source laws 4 → 5 (V179/op28 added, P6); canonical endpoint premises removed: 0. Target not yet established.

op26: split no-stub gate resume-join-one-byte-01 passes base/suffix lengths 0–1, arbitrary bytes/index. Owned return extraction retains structured Drop failure. Mutable-reference extraction also rejects escaping reference outputs (aeneas-source-join-mut-opt-resume-01). No row credit.

op28: owned identity String reference extracts without callbacks or Drop. Lean 43000/43001/43004/43005 accepted; 43002/43003 rejected, no failed proof artifact accepted. P6 native gate resume-string-path-01 passes all valid UTF-8 length-2 strings, arbitrary byte index, exact content/length; no deployed-toolchain association inferred. Stable bundle op28_source uses StringTypes/selectedString; prior names remain unchanged. The four previous laws remain available on selectedAll; inherited selectedString preservation checks at 43008 failed on an unclosed section; corrected source accepted at 43009.

op30: native content/capacity gate resume-string-capacity-01 passes n≤4. Direct optimized extraction hits Aeneas Z.Overflow; owned reference calls unresolved alloc.string.String.new. This is not a closed source law. Capacity/allocator effects not erased from native evidence. op32 retains its exact NATIVE-EFFECTS.md deferral.

All new native/extraction runs have collected-receipt.json; numbered Lean receipts include full target, exit, wall, RSS, swap, revision and axioms. Kani gates are small control/index checks only. No SHA Kani run is permitted or performed in this resume.


After op30: including String.new produced has_errors=true despite Charon exit 0 (unsupported ConstEvalVal / dangling zero-allocation pointer during constant conversion); Aeneas was correctly not launched. This is a translation failure, not a checked Rust execution or ROW counterexample.

op31: optimized exact push_str extraction reaches the escaping-reference preflight; native split gate resume-string-push-r01 passes valid UTF-8 two-byte source plus one-byte suffix, full length and arbitrary output index. No source law credited.


op33: retained-owned adapter avoids abandoning the input, but its exact extraction still rejects structured Drop (aeneas-source-op33-retain-opt-resume-pop-retain-01). Loop-free error-empty/singleton gate resume-pop-errors-r01 passes every Error variant. No generic pop row credit.

SHA: direct private helper start-from diagnostics emitted empty function modules; these are not accepted extractions and confer no source credit. The full dispatcher does have a nonempty exact body but fails loan preflight. A byte-matched owned fallback helper module now extracts the scalar two-round function without callbacks, accepted at 43010; schedule port exposed a signed-shift RHS backend type mismatch, rejected at 43011. The reference now explicitly types the literal shift 10 as u32 (same positive bit count); that port is documented in fallback-reference-source-map.json and needs regenerated evidence. This is explicit supporting work on the false dispatch branch only.


op36: retained-owned Vec adapter still rejects escaping reference outputs (aeneas-source-op36-retain-opt-resume-array-retain-01). No generic-array/reference preflight was disabled. Native full array gate is next. No row credit.

Fallback scalar two-round shape is proved at 43015: on arbitrary scalar words, the extracted helper returns exactly the packed two successive scalar steps, retaining the full Result. This is not accelerated SHA compression or an op208 source law. It uses symbolic U32 operations and four-element shape/index lemmas, without evaluating a 64-round concrete recurrence.
