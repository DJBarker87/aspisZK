# S5 concrete dot to the stage-2 residual equation

The checked component now supplies the existing `Stage2FinishAccumulator.DotLaw`; the entire dot-product equation is no longer an assumption. The new theorem `finish_residualBatch_of_reader_interpretation` composes that law with successful execution of the same typed finish and the retained accumulator theorem to derive the 22-query residual sum is zero.

Evidence: `lean-candidates/s5-stage2-dot-residual-composition-20261020/`. The source endpoint, unchanged control/pairing/accumulator consumers against the one-sided naming adapter, selected import owners, producer receipts, standard-only axiom reports, admission and resource receipts are retained. The endpoint passed in 4.513s on the NUC with zero swap. No full replay, production source edit, artifact rebuild or deployment was performed.

The dependency chain is actual successful kernel execution → ordered source message/weight reads → indexed source product sum → individual read interpretations → exact existing typed R14 DotLaw → successful finish comparison plus accumulator invariant → residual equation. It reuses the previous decoded-product/source-trace proofs and existing R14 accumulator theorem.

Still OPEN, explicitly:

- The individual final-message parser reads must correspond to the authenticated matching data `d.f` (R13/reader binding).
- The actual accumulator weight slice must have length64 and its read values must correspond to the model weights (S8/R15).
- The supplied model weights and RHS must satisfy the checkpoint/query accumulator invariant (S8/R15).
- The stage-2 backend comparison and two-fold geometry must hold for the actual caller.
- `withSourceDot` is a checked candidate backend installation. The frozen Rust caller must be shown to install/refine it; the theorem does not establish that by defining the candidate.
- Whole source/runtime/artifact correspondence, the remaining final-theorem hypotheses and global100-bit soundness remain open.

The joined import initially exposed the existing generated discriminant instance collision. A reversible naming adapter and identical original/adapted constructor-code audits are in `lean-candidates/s5-stage2-dot-reader-backend-20261020/`. The final integration also exceeded Lean's internal -M4400 guard during imports: a distinct import-only diagnostic reproduced the failure before any theorem elaboration. A documented NUC-only -M6000 selected integration retained the same OS High1GiB/Max2GiB/Swap0 cap. There was no cgroup memory-pressure/OOM/swap event and no large-term reduction; local compile policy is unchanged.

The mathematical result is proved for the named model/backend and explicit hypotheses. Frozen-caller installation and implementation-linked 100-bit closure are not proved by this packet.

## Source comparison component

The follow-on packet `lean-candidates/s5-stage2-source-comparison-residual-20261020/` additionally reuses checked `finish_eq_success_true` to supply the existing comparison law. Its `finish_residualBatch_with_source_dot_ne` no longer takes a complete-dot or comparison-law premise. Individual reader meanings, the accumulator invariant, two-fold route and actual frozen backend/caller installation remain open. No canonicality assumption is needed to infer decoded equality from raw source equality; this does not remove the separate arithmetic/range/canonicality obligations.
