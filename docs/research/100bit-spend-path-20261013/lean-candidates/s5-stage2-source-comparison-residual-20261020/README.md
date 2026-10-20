# Stage-2 source comparison and concrete-dot residual equation

PROVED: `sourceNe_false_decode` reuses the retained checked `finish_eq_success_true` source equality theorem. A successful false result of the mapped source inequality implies equality of decoded fields, without any canonicality premise for the comparison itself. This is one-way sound comparison; it does not discharge arithmetic canonicality/range obligations.

PROVED: `installed_source_comparison_law` supplies the exact existing Stage2 ComparisonLaw for `withSourceDotNe`. `finish_residualBatch_with_source_dot_ne` composes that source comparison with the previously checked concrete dot and existing R14 accumulator theorem. The whole dot equation and a separate comparison-correctness contract are both conclusions/components, not premises.

Explicit remaining premises: ReaderMeaning (actual message/weight reads, slice length64), checkpoint/query accumulator invariant, two-fold route, successful typed finish execution, and actual frozen caller/backend installation. `withSourceDotNe` installs the mapped checked source primitives in a candidate typed backend; it does not establish that the frozen Rust caller refines/installs that record. R13/S8/R15/source/runtime/artifact/global100-bit closure remains OPEN. No Rust, ELF or deployment changes.

Focused NUC Lean4.32 target passed -j1/-M6000 (same selected import-union guard documented in the preceding packet), High1GiB/Max2GiB/Swap0,2.408s, processRSS4665912KiB, cgroup447262720B, zero swap/pressure/OOM. All three exported theorem audits use only propext, Classical.choice, Quot.sound. Existing equality/kernel/control/accumulator proofs and caches were reused; no dependency or manifest replay.
