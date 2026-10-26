# Stage 1: installed successful return inversion

SAF_Returns.round and SAF_Returns.finish compile in SAF_002. Both audit to
[propext, Classical.choice, Quot.sound]. SAF_001 failed on a dependent rewrite;
the replacement transports the round1 successful call before rewriting its
result. No failed source was rerun unchanged.

SAF_FinishSaved.strengthen compiles in SAF_003, standard axioms only. It uses
the existing accepted installed finish observation to construct RoundValues,
weights/pair/dot, all fifteen return laws, and the successful comparisons.
Its continuation retains PairingLaws, matching, EquationEndpoint, dot meaning
and canonicality. No new Prop-law hypothesis is introduced. The existing
input/model/trace and successful native finish call remain unchanged.

This is not yet a top-level premise-removal claim; composition follows.
Receipts include exact commands, source/dependency hashes, source revision,
exit, wall, peak RSS, swap, scope limits and all printed axioms.
SAF_002: exit0, 5.920533207s, 4372888KiB, swap0.
SAF_003: exit0, 5.845095561s, 5255368KiB, swap0.
Budget: 3 Lean invocations (2 pass, 1 excluded development failure), 0 Kani.
