# S7, S8 and checkpoint composition review

Base: `4ca5d2e35`, branch `codex/cx-cones-p6-20261021`.
Only additive modules and this packet's tools/evidence are owned here.
No shipped source, sibling or protected candidate is edited.

## Stage 1: S8 returned-state finish

`S8P6ReturnedFinish.mutable_certificate` composes the existing complete
mutable finish with exact field interpretation, on arbitrary old contents,
raw U64 limbs, term counters and unused raw suffixes. The caller supplies
only destination length=64, destination<=raw length, and the 64 reached raw
field values equal to the **returned** accumulator's weights. Neither
whole-function success nor dot/output equality is assumed.

`finish_certificate` proves full Result equality for that traversal followed
by the explicit field-reference dot/check, including false results.
`stage_observation` substitutes it into frozen2 stage2 for **any returned
accumulator**, preserving all batch1 addresses/answers and the Bool.
This avoids identifying the returned state with an independently chosen
run22. It is a finish-port certificate, not a complete source S8 certificate:
`finish_query_dot` and `finish_relation` are not renamed the field reference.

Validation: `S8P6ReturnedFinish`, attempt 2, exit 0, 7.755517040845007 s,
peak RSS 3,631,808,512 bytes, zero swaps, source revision
`4ca5d2e35` (full revision/SHA/dependency fingerprint in receipt). All three
`#print axioms` reports are `[propext, Classical.choice, Quot.sound]`.
Attempt 1's elaboration failures and recovery axiom lines are retained and
excluded from accepted evidence. Local Lean v4.32.0, -j1 -M4400,
-DElab.async=false, shared mkdir lock, private object directory and
`/usr/bin/time -l`. No shared object is overwritten.

The new manifest is `cones-p6-manifest.json`; inherited multiproof evidence
and `manifest.json` are unchanged. No host/Kani/SBF build or full regression
has been run. The conditional shipped-file/ELF rebuild gate is not triggered.

## Scope check before whole-function claims

S7JoinFrozenConsumer.decision_eq and S8JoinFrozenArithmetic.decision_eq
both target **dV_frozen**, not dV_frozen2. Checkpoint pass 5 does target
frozen2. All three inherited STATUS files explicitly retain source adoption
obligations; none supplies an already-instantiable whole-source certificate.
The next stages inspect those exact local gates rather than assuming the
missing complete-function equations as P6 fields.
