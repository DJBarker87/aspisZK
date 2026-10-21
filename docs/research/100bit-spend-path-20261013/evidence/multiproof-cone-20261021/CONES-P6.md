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

## Stage 2: S7 complete accumulator-port iteration

`S7P6AccumulatorIterations.total` composes the inherited complete one-query
accumulator carrier port for every transaction-local count within 22.
It derives each call's success, canonical RHS/power, unchanged output-weight
storage, all 64 exact coefficient updates, raw PushTrace membership, phase
progress and final cursor. The caller supplies the initial reached invariant,
canonical rho/values and count bounds, **not** any per-call success or step
correspondence. `Trace` retains each actual port execution and full local
coefficient/RHS/power equations. This covers the accumulator portion of
both 10- and 12-step intervals without normalizing a concrete run.

It does not certify the frozen `query_values`: the opening, four_dots,
circle comparison (including Query rejection), line fold, geometry lookup,
and source carrier/observer lowering must first produce those node/value
inputs and adopt the port. No source query gate is silently replaced by an
always-successful accumulator call.

Validation: `S7P6AccumulatorIterations`, attempt 1, exit 0,
4.882670667022467 s, peak RSS 3,377,020,928 bytes, zero swaps, revision
`9c8429300` (full revision and all pins in receipt). Its `total` axiom report
is `[propext, Classical.choice, Quot.sound]`. The same fixed local compiler,
flags, lock and private objects were used. No source/ELF/host build changed.

## Stage 3: complete emitted K writer to C5

`CheckpointP6EncodeK.encode_k_total` proves the complete emitted `encode_k`
returns all four words' LE bytes, for arbitrary raw U32 limbs. It composes
both actual nested CM31 writers, all checked sub-slices/copies, and their
back-write continuations. No per-write success law is assumed.
`CheckpointP6KBytes.word_bytes` proves arbitrary-word source LE bytes equal
frozen le32. `encode_k_c5` composes the whole writer with pass 5's C5
canonical representation theorem, giving exact C5.encodeK output bytes.
Canonicality remains required only for the quotient/physical-byte bridge;
it is unnecessary for writer success. The inherited `not_all_words_canonicalized`
counterexample explains why deleting it would be false.

Successful validation (exact full revisions and pins are in receipts):

| Target | Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps | Revision |
|---|---:|---:|---:|---:|---:|---|
| CheckpointP6EncodeK | 2 | 0 | 16.534316333010793 | 3656187904 | 0 | 9c8429300 |
| CheckpointP6KBytes | 9 | 0 | 24.81911849975586 | 3666837504 | 0 | b296751fe |

All three theorem axiom reports are `[propext, Classical.choice, Quot.sound]`.
The initial writer attempt needed explicit monad-lift/back-write unfolding.
The byte bridge's failed attempts exposed recursive simplifier interactions
between BitVec.toLEBytes, UScalar.val and bv_toNat, plus small elaboration
issues. The permanent replacement exposes just four symbolic bytes and
uses explicit BitVec/Nat equalities. No recursion/heartbeat/memory setting
was increased; failed recovery output is excluded. The small norm_num
invocations normalize only byte-width powers/division-by-one, never a
concrete checkpoint vector or recurrence. No solver or full-build rerun.
