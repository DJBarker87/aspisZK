# PCWU_ANALYSIS_2: limitation (2), returns inside nested loops and breaks to outer loops

## Reproduction
PCWU_E004 (TV3; root verifier::prepared_claim; trace::value opaque) gives `[Error] Returns inside of nested loops are not supported yet`, verifier.rs 53:0-68:1, and the body is ignored. The `?` on `dot.push(..)` sits in `for l in 0..29` (depth 2) inside `for point in 0..6`.

## Cause (TV3 source)
- PrePasses.ml `update_loops`: `visit_statement` asserts `depth <= 1` for Return (TV3 line ~676), and `visit_Break`/`visit_Continue` assert index 0 (~665). Transformations 1-3 (plus PCWO patch A) only move a depth-1 return out of one loop.
- The symbolic interpreter supports only one-level exits too: InterpLoops.ml `eval_after_loop_iter` asserts `i = 0` for `Break i` and `Continue i` ("Nested loops are not supported yet", ~180 and ~310). Removing the pre-pass assertion alone would fail there.
- Applying transformation 1-3 recursively from the innermost loop (the PCWH_ route) is not sufficient. A depth-2 return must leave two loops, which needs a multi-level exit or carried state. A Bool flag plus the return place `_0` fails as well: at the inner loop's break join `_0` is bottom on the normal path and a value on the return path, and the join yields bottom.

## Proposed general fix (upstream style, no Aspis names)
This is a new pre-pass before `update_loops`, "nested early-exit lowering". For each Return at depth d >= 2:
1. Before the innermost enclosing loop statement L, insert `exit_L := Option::None` with a fresh local `exit_L : Option<RetTy>`. Find `core::option::Option` in the crate by name (it is already pulled in by `--include core::option::Option`). If it is absent, keep today's error.
2. Replace the Return by `exit_L := Option::Some(move _0); Break 0`.
3. Directly after L, insert `switch exit_L { Some => { _0 := move (exit_L as Some).0; Return }, _ => {} }`. That Return is now at depth d-1, so repeat until depth 1, where transformations 1-3 apply unchanged.
The fresh local is always initialised, so break joins see a symbolic Option rather than bottom, and `_0` is only written on the path that returns. A Bool exit local handles Break i / Continue i (i >= 1) the same way (verify_in_place).

Semantics: this is equivalent to the source control flow, with no Aspis special-casing.
Emission shape: an extra Option-typed loop output. A fresh = gate proof must then go through the loop invariant, not rfl.
Upstreamable: plausibly yes as an opt-in pass. Upstream tests needed: nested-loop return with and without values, return under several nested switches, Break 1 and Continue 1, and drop/StorageDead in the exit path.
Cost: about 150 lines of OCaml against Charon 454586e9 LLBC (`switch_data` with branch lists, `Assign`, `Aggregate` of an ADT variant, a field projection on a variant). Next round: write it, typecheck it in a TOOL-BUILD scope from image pcwo-aeneas-pair:t001, then run E-scopes on prepared_claim and verify_in_place.
