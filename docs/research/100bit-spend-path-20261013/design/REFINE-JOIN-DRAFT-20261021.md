# Accepted execution refinement — unmerged draft, 21 October 2026

Branch `codex/cx-refine-join-draft-20261021`, based on inner-order draft
`d1ed5eed9`. The lead must not merge this packet before user approval of the
oracle port. Existing Lean modules, candidate re-pins, M10 and shipped source
are read-only. This packet uses new `OraclePortRefineJoin*` modules only.

## Accepted execution interface

`OraclePortRefineJoin.ExecutionRefinement D rust` is verbatim:

```lean
AcceptedRefinement rust (verifier D OraclePortShortCircuit.outerDecision)
```

`AcceptedRefinement source model` is verbatim:

```lean
∀ H i, (eval H (source i)).2 = true →
  (eval H (model i)).2 = true ∧
    (eval H (source i)).1.Subperm (eval H (model i)).1
```

`i : Input` preserves the public statement, proof function and stored bytes.
The oracle world is the same. `execution_join_refines` proves the inherited
`ExecutionJoin` implies this predicate; `outer_join_refines` covers the
outer-short-circuit join. `accepted_budget` gives 1161 queries on accepted
source runs; `accepted_no_extra` gives containment of each source read.
`rejected_read_refines`/`rejected_read_not_equal` witness strict weakening
for every model with a rejecting input. Nothing bounds rejected source runs.

## Consumer obstruction: containment is not extraction transport

The consumer's event is
`run.accepted ∧ RawRecordedPublicSpendExtractorBin.extract run coins = none`,
not acceptance alone. `runtime_transport` currently rewrites the whole
accepted annotated run. Its constructor `annotatedWith` records one execution,
uses `build D` to enrich the proof, then runs the verifier again.

`OraclePortRefineJoinRecoveryObstruction` compiles two countermodels:

* `sparse_refines_rich`: a source which accepts without reading refines a model
  which reads one leaf and accepts, for every input and oracle. The actual
  `RawCutRecordedWordsExecutableBin.recoverAtExec` returns `none` on the source
  log and `some ([],salt)` on the model log. The witness uses width zero and an
  empty path to isolate the same primitive used by the production extractor;
  it is not a valid full protocol proof.
* `cut_permutation_counterexample`: equal full read multisets can have different
  `cutBeforeExec` prefixes. Moving a leaf across a frame loses it from the cut.

These refute a generic recovery-preservation rule from the proposed
containment direction. They do **not** refute `dV_sc` soundness, the desired
full protocol theorem, or the frozen slot's accepted-run refinement. The
missing protocol-specific argument must show that the frozen execution has
all recovery-relevant reads before the same commitment cuts (and gives the
same annotation words), or change the runtime/extractor to replay the model
and prove its cost/observation contract. A query budget alone gives neither.
One must also account for the two passes of `annotatedWith`; arbitrary Rust
programs need not preserve acceptance under proof enrichment.

Consequently there is no claimed `OraclePortHeadlineRefine` with the requested
signature in this packet. No premise deletion is claimed. R19 and the existing
draft endpoints remain unchanged. The exact candidate signature replacement
and the failed transport step are recorded in evidence; this is an obstruction
to the proposed black-box proof, not a full-verifier counterexample.
