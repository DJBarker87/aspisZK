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
