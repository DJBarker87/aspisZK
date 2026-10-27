# Resume 2026-10-27

Baseline c35956a836; Env-J 43000–43299, new 100 Lean / 8 Kani budget, last three charged Lean attempts reserved for bundle audits. Prior tally retained as TALLY-prior.json. Source laws 4 → 5 (V179/op28 added, P6); canonical endpoint premises removed: 0. Target not yet established.

op26: split no-stub gate resume-join-one-byte-01 passes base/suffix lengths 0–1, arbitrary bytes/index. Owned return extraction retains structured Drop failure. Mutable-reference extraction also rejects escaping reference outputs (aeneas-source-join-mut-opt-resume-01). No row credit.

op28: owned identity String reference extracts without callbacks or Drop. Lean 43000/43001/43004/43005 accepted; 43002/43003 rejected, no failed proof artifact accepted. P6 native gate resume-string-path-01 passes all valid UTF-8 length-2 strings, arbitrary byte index, exact content/length; no deployed-toolchain association inferred. Stable bundle op28_source uses StringTypes/selectedString; prior names remain unchanged. The four previous laws remain available on selectedAll; inherited selectedString preservation checks accepted at 43008.

op30: native content/capacity gate resume-string-capacity-01 passes n≤4. Direct optimized extraction hits Aeneas Z.Overflow; owned reference calls unresolved alloc.string.String.new. This is not a closed source law. Capacity/allocator effects not erased from native evidence. op32 retains its exact NATIVE-EFFECTS.md deferral.

All new native/extraction runs have collected-receipt.json; numbered Lean receipts include full target, exit, wall, RSS, swap, revision and axioms. Kani gates are small control/index checks only. No SHA Kani run is permitted or performed in this resume.
