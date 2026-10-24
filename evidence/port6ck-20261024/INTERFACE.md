# Observation quantifier audit

Before (`Port5Q2_Advance.ObservationBinding`): value/basis for every
`a out b bout` and every `Observation ... a ...`, at arbitrary `a.next.val`.
Q1's `Observation.fields` cannot establish this: its geometry binding applies
only when `start.val <= a.next.val < end.val`.

After (`Port6CK_Advance.ObservationBinding ... lower upper`): value/basis for
those same observations, with two extra arguments `lower <= a.next.val` and
`a.next.val < upper`. Iota and rho fields are unchanged. No loop output,
accumulator equality, reader success or additional authentication premise is
present. This is an additive interface; Q2's module is untouched.

Sufficiency: `Port6CK_Advance.calls` requires only the initial lower bound.
Each actual `Calls.step.active` supplies next<end, and the SAME source query's
`query_fields` supplies next'=next+1. The lower bound propagates by induction.
`Port6CK_Ten.reached` instantiates lower0/upper10 from the actual S2 initial
constructor and actual ten-step call sequence. It retains all Q2 prepare,
basis, arithmetic and canonical-line ports, but consumes the reached interface.

Concrete value/basis instance: `Port6CK_Binding.from_observation` applies
`Port5Q1_Observation.fields` with those exact bounds. SAME proof, Prepared,
parsed bytes, data, rho, query sequence and geometry. Q1's exact authenticated
premise `forall pos, pos<22 -> recovered(index q 2 pos)=some(payload parsed 2 pos)`
is retained verbatim. Authentication is not discharged by this job.

This establishes the local observation-to-ten induction path, not an
instantiated native op18, whole-TX agreement or a release result.

# Final saved/resumed statement audit

Before (`Port5Q1_Complete.accepted`): both source blocks share one literal `p`;
the second pending/query calls take exactly `materialize out10 flushed10`.
The same saved-to-resumed physical state is therefore a caller obligation.

After (`Port6CK_Complete.accepted`): ONE actual installed TX1 returns `saved`;
CURRENT op18 consumes `checkpointSlice saved` and returns `(p1,a1)`. Second
geometry/pending/query/flush cuts use those exact returned fields. There is no
first-loop argument and no cross-TX equality or independent retained-reader
success premise. `Checkpoint.accepted` derives p1=pSaved/a1=aSaved from the
actual writer input and complete canonical physical roundtrip. `Saved.accepted`
derives its ten-step model state from THAT writer prefix and the reached Q1
observations. The second source block advances THAT returned a1 by12 and
materializes `OraclePortFrozen2.completeState i q`.

The first g is the actual op7 return selected by the prefix. The second g2 is
an explicit actual resumed query operand (upstream powers/op17 remains owned
by Session A). They are not freely selected model accumulators. The SourceInputs,
parsed proof bytes, literal matching read, rho and q are shared exactly.
Q1's authentication quantifier is unchanged. Preparation now has ONE named
`Port6CK_Owner.SessionAPrepare`: canonical immutable fields plus SAME-input
query/rho/alpha1 semantic bindings. ONE named primitive interface retains Q1's
query/basis/decoder/arithmetic, geometry and domain interpretations. Neither
interface contains checkpoint/loop/output agreement or a model accumulator.

`Port6CK_Ordered.accepted` transports the complete checkpoint six-read result
to the CURRENT reader program itself, not just the retained reader's effect
program. `combined_run` reconstructs the SAME writer-before/reader-after log;
the accepted reference run's determinism identifies the final log literally.
