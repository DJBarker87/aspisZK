# S1 initializedness API assessment

Native Claims initializedness is NOT proved. The 769-check normal-return row-step gate and the two uninit-checks compiler ICEs retain their original scope. This note rejects a proposed API-only workaround; no compiler, solver, backend modification or host scope was launched for it.

Inspected the upstream Kani 0.67.0 tag at commit 4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d. The complete four inspected source files, URLs, hashes and relevant locations are pinned in evidence/s126-current-caller-20261021/s1-init-api-assessment-20261024. This is upstream source inspection, not a new binary/source correspondence attestation for the historical native gate.

The public can_dereference function calls assert_is_initialized; is_initialized itself is crate-private. Crucially, the compiler's IsInitializedIntrinsic lowering returns constant true when enable_uninit is false. Adding mem-predicates to the old default-check harness therefore cannot establish initializedness. Enabling uninit-checks remains necessary for this API route, so the existing FieldsShape::Primitive/ValueAbi::Scalar compiler failure cannot be bypassed merely by adding that predicate. No success claim, rerun or larger cap is warranted from this finding.

Primary pinned sources: [mem.rs](https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/library/kani_core/src/mem.rs), [intrinsic lowering](https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-compiler/src/kani_middle/transform/kani_intrinsics.rs), [layout computation](https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-compiler/src/kani_middle/transform/check_uninit/ty_layout.rs).

Read-only audit: `python3 tools/s1-init-api-20261024/check.py`.

Next native deliverable still needs a validated initializedness/source route, shipped allocation/error/drop/full-loop association and composition into the enclosing Claims implementation instance. The new source-bound SDK preparation/claim/challenge theorems do not discharge these. Heavy jobs still require fresh reviewed admission; none is inferred from an offline resource candidate or historical cap. S1/S6 and <=2^-100 per-attempt soundness remain OPEN.
