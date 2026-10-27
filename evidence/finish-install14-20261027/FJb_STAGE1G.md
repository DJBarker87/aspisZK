# Stage 1G: native M31 rounds and literal initial constants

FJb_M31Step.value086 checks the actual mutable-index/backward-update/read-again
cell,including overwrite and canonicality. The value is the SAME source cell
plus SAME M31 constant,to the fifth power. FJb_M31LoopStep095 and
M31Loop096 check BOTH actual nonlinear traversals symbolically.
FJb_M31LazyRound.value097 composes the ORIGINAL loop and complete native
external layer into literal R0P.poseidonFullRound on the SAME operands.

FJb_InitialConstants099 checks actual table reads,ALL4x16 literal U32 bounds,
and their literal R0P initial-constant meaning. This is a small fixed table:
no round,permutation or recurrence is evaluated.098 omitted Array.make from
its simplification set;099 adds that constructor unfolding,without changing
limits or repeating an unchanged compile.

097:exit0,wall2.0300688040442765s,peak3863892KiB,swap0.
099:exit0,wall3.9046565979951993s,peak3902964KiB,swap0. Both standard axioms
only. Full target,argv,revision/hash,deps,cgroup and audit text in receipts.
087/089/091–094 failed to factor a typed mutable tuple continuation.095 proves
the factor by explicit bind congruences,tuple elimination and a symbolic
changed goal before associativity. No new admission or P6 boundary was added.
Two supporting generic tuple lemmas(088/090) are valid but were insufficient
for the native generated matcher. No source loop reached10 failed attempts.

FJb_LeadingMiddle and ExternalZero are archived unchecked proposals,with the
separate statement-print wrapper superseded by the combined final audit.
They are not delivered proof roots or credited progress. Final audit attempt100
will import every current passing FJb module,FJa_Audit,and the inherited actual
tops/non-vacuity theorems,then print every new theorem's axioms and all four
inherited kernel statements. No package or frozen-manifest replay.

No deployed premise removed. Native leading final packing,interpolated full/
internal pairs,all projected evaluator channels,complete composition/literal
transport,and deployed installation remain as in FJb_ROWS.md.
