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

## Whole-function composition blockers and exact next gates

**The requested whole S7/S8/checkpoint function certificates and their
instantiation are NOT supplied.** The local additions above do not change
that status. In particular, no unproved function equality was installed as
an axiom, boundary field, verified solver stub, or renamed reference.

The inspection disproves the handoff's assumption that each retained stage
join was already a frozen2 join waiting only for such certificates. S7 and
S8's retained complete decision equalities target frozen1. The new S8 stage
bridge resolves its returned-state/frozen2 mismatch only for mutable finish
plus the field dot. Checkpoint pass 5 already supplies a frozen2 reference
stage equality. This distinction is visible in the theorem definitions.

1. **S7 / external S4 dependency:** `query_owned` does call the actual
   `fast_dots.four_dots`, then the circle check and line fold. Its extraction
   manifest marks 24 functions opaque, including four_dots, wide raw-byte
   decode/arithmetic, literal domain reads and inverse; its required
   TypesExternal/FunsExternal implementation modules are absent from that
   retained generated packet. Several independent replacement ports are
   proved, so 24 is an extraction-boundary count, not a claim that all 24
   lack any local theorem. The authoritative S4 audit row still has only
   successful-call helper witnesses/outer residues, without complete output
   field meaning or totality. Needed next is the four returned field-value
   equations for the reached opening and scratch powers, then the circle
   comparison/error and line-fold backend joins. Those S4/S5 semantics are
   more than S2/S10's physical-carrier/caller binding. Protected Session A
   candidates were read only; none was edited or credited as adopted.
   The new iteration theorem cannot turn arbitrary supplied canonical values
   into these missing source-produced values.
2. **S8 / external S5 dependency:** the source final check calls
   `EbyKDot::new/push/finish` via `finish_query_dot`, inside relation-round and
   pairing guards. The retained S5 finish theorem assumes comparison/pairing
   laws and successful finish. It does not certify the all-result final dot.
   Needed next is a reachable-count one-push contract with exact two-QM31
   raw updates, then count/64-term induction, canonical final conversion,
   source field reads and Parse/Query error composition. The mutable finish
   certificate does not discharge those calls. Calling the reference field
   sum a source P6 operation would hide the desired whole dot equality.
3. **Checkpoint / byte and dependency gaps:** the new K writer closes a
   real primitive gap. Extracted e_byte and sparse body_byte still need
   exact C5 byte equations, followed by all 18 body blocks and checksum;
   strict reference decoders need complete C5 output/rejection meaning and
   production section/allocation/reader composition. Bounded Kani field,
   authentication and section gates are not the complete decoded C5 state.
   Actual prepared/initial/saved/resumed RHS/power/weights provenance also
   depends on the unfinished S1/S7/S8 source joins. Needed next is the
   extracted E-byte theorem and fixed-block byte/decoder composition, then
   source-state adoption at the existing strictStage/reached_stage endpoint.
   CFG chronology and next=10/22 alone do not establish these fields.

These are explicit source-semantic dependencies absent from the retained
certificate set, not mathematical counterexamples to the ultimate cone
statements. S2/S10 caller binding and the named lowering boundaries remain
separate, as requested. There is no global AcceptedRunJoin, premise removal,
or established deployed 100-bit claim. No change to the security target.

The final scope/source/function/receipt ledger is `cones-p6-audit.json`.
It pins every relevant current Rust function body, the inherited extraction
manifest and exact opaque-function inventory, all current new sources,
object/dependency hashes, accepted axioms and failures. Recheck with
`python3 -B tools/cones-p6-20261021/audit.py`; this performs no solver replay.

## Final focused verification and handoff

`ConesP6FocusedFreeze`, attempt 3: exit 0, 8.702210166025907 s,
peak RSS 3,629,465,600 bytes, zero swaps, revision
`2e271a6cc` (exact full revision/source/dependency hashes in receipt).
It imports the four new proof modules, the inherited checkpoint decision,
and the unchanged frozen2 cone/headline consumers. All ten union axiom
reports are `[propext, Classical.choice, Quot.sound]`; together with the
seven principal theorem reports there are 17 accepted reports. The two
failed union attempts lacked the module containing the cone constructor;
those errors are retained and excluded, then fixed by importing
OraclePortFrozen2Cones. No source proof was retried unchanged.

`python3 -B tools/cones-p6-20261021/audit.py` exits 0: five current modules,
17 reports, maximum peak RSS 3,666,837,504 bytes, zero swaps. The source,
object, exact function-body, source-scope and inherited dependency checks
pass. `git diff --check` passes. This is one focused compatible-cache union,
not a coherent frozen release manifest replay. No full solver, adversarial,
runtime, Rust or SBF rebuild ran; unchanged historical gates are cited only
at their retained scope. No shipped file or protected/sibling module was
changed, so the conditional frozen-ELF rebuild gate was not triggered and
no new byte-identity measurement is claimed. No key/wallet operation,
shared-object overwrite, push or merge occurred.

Both requested whole-cone deliverables remain blocked on the explicit
source-semantic dependencies listed above. The next owner handoff is the
S4 four-dot output meaning and S5 dot/finisher source laws, plus the remaining
checkpoint E/body/strict-decoder joins. The new local results are ready to
compose once those interfaces and the S2/S10 reached caller binding exist.
