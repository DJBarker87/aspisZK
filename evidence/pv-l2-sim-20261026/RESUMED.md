# L2 continuation from 36717b11ae

Branch `codex/pv-l2-sim-20261026`. Fresh allocation: 100 Lean attempts,
20 Kani runs; Env-J 21900–22199. The predecessor's 100/20 is separate.
This file records the continuation; REPORT.md retains the historical report.

## Fixed target and row identities

The actual endpoint remains
`PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`, with unchanged
`simE`, observer, charged events, and artifact pins. No crates/programs edits.
The root checkout and other worktrees are read only. Research evidence is
read with `git show research:<path>`.

The requested inversion row is called **V380 (inversion, D197 escalation 2)**
in this report. At the inspected research revision, V380 already denotes
`TrustedStd.btree_entry_or_insert_with`; those are distinct obligations.
The collision must be resolved by the lead; this worker does not edit the
shared ledger or reassign a trust item.

## Validation accounting

J21900 initially returned shell exit 126 because the launcher lacks its
executable bit. Invoking the same script with `bash` launches it without
changing infrastructure. The failed shell invocation launched no compiler
and consumed zero attempts. The eventual J21900 compile is counted normally.
Every subsequent compile uses the shared launcher, -M7000, 6G/8G/swap 0,
TasksMax 128 accepted by lead ruling (b). No unchanged failed source is
rerun. Per-attempt source snapshots and resource/axiom receipts accompany
this file. Failed elaboration `sorryAx` prints are not proof evidence.

## Work in progress

`PV_L2_F3FullSource` produces both count-law values and ordered actual-owned
read records. Refills carry the extracted frame, including failures. Its
outer record survives None, and the second stream is not called after the
first fails. Native E1/L1/ROM instantiation and joint simulation remain open.

## Inversion evidence (V380 inversion)

`PV_L2_InversionQ.branch_nonzero` proves that the actual extracted QM31 zero
test returns `ok false` for a canonical operand with nonzero decoded value.
`logup_operand` produces the actual source subtraction result for chi-slot,
its canonicality, nonzero value, false zero test, and successful extracted
inverse, from canonical chi/slot and their decoded inequality. Inversion
success is a conclusion, not a premise. `PV_L2_InversionPole.producer` and
`consumer` derive that inequality from the existing model `NoPole` at every
active row/slot, retaining the explicit native-slot-to-model equality.
Neither theorem restricts to successful P_R1 challenges.

Source anchors: `crates/aspis-statement/src/logup.rs:199–214`; selected
pre-helper guard `crates/aspis-r1-cost-probe/src/host_semantic.rs:247–258`
and `273–297`. **OPEN as a whole row:** native call enumeration and slot
association remain unproved. Generic CodeField, WideExact, interpolation,
quotient-pivot, circle/fallback and certificate paths remain required.
Inherited source/overflow/canonical-arithmetic boundaries are retained.

Fresh Kani allocation: **20/20 charged**, 17 successes, one CLI rejection,
one source-assembly rejection, one proof-side memcmp unwind failure. The
replacement for the last uses pointwise limb comparisons (z09), without
raising its failed bound. No old timed-out harness was rerun. The 13 exact
source items are pinned to rebase candidate
`351c5c7f6b6ac0110459192ef1c55e25a6c80c67` in
`tools/pv-l2-sim-20261026/zero-source-binding.json`, explicitly distinct from
this branch's unchanged crates/ tree. No arithmetic/inversion stub exists.
Checks cover CT zero predicates, canonical successful limb/byte decoding,
roundtrips, wrong-length rejection (0–33 except 32), selected invalid limbs
and an arbitrary selected nonzero limb. These are leaf/representation
results, not native caller reachability or a complete V380 discharge.
No witness attack has been established. z01–z20 retain resources, output,
source snapshots/hashes and exact harness targets.
