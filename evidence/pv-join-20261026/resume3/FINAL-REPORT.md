# pv-join3 resume report

Branch `codex/pv-join-20261026`; starting revision `ce8e0224ab`.
Target not yet established. No endpoint premise is removed, weakened, or added.
No checked shipped-source ROW counterexample has been found.

## Baseline

Required first attempt 36500 failed on missing `PV_Join_FieldCaller.olean`.
Attempts 36501–36578 reconstructed the missing audit dependencies in order.
The original combined audit checked at 36579: exit 0, wall 0:03.22,
peak RSS 4,315,932 KiB, swap 0, 57 standard-axiom reports. This is focused
closure evidence against the restored cache, not a complete release replay.

## Fixture obligations

For transfer and withdrawal, the independent byte equation, complete
model audit/status equation, whole V163 equality, and native non-vacuity
remain open. `fixture-obligations.json` records this explicitly.

Neither an execution trace nor a reachability proof is available for either
fixture. The source fixture preparation does not fix the attempt secrets,
nonce-store state/acceptance, or hash/oracle behavior. **Reached entries:
unknown for both fixtures. Unreached entries: none established.** No entry
is excluded from the fixture obligations on static inspection alone.

The inspected rw20 branch provides independent serialization on mathematical
fields/queries/slots, but explicitly lacks their construction at the deployed
caller input. `sibling-read-only.json` pins the inspected revisions, and
`rw20-model-boundary.lean.txt` retains its statement. No sibling file was edited.
cb4's only matching remaining-inventory source declaration is op259 in a file
marked PREPARED, with fresh extraction/type-check pending; no joined source-law
credit is taken.

Inventory **30 → 30**: 4, 32–36, 79, 117, 121–123, 132–134, 222–224,
226–228, 230, 232, 249–253, 257–259. No side-channel, native-world, entropy,
release-artifact, compiler-success, or actual client association is discharged.

## Focused consumers and final audit

Inherited `ClosureCheckpoint`, `Inspect`, `NativeNeg101`, `PublicOp20`,
`AuditProjection`, and `LedgerSource` checked at 36580–36585. The new
`PublicDataIff` checked at 36586. It proves the exact equivalence between the
complete selected public-caller Result with canonical model audit and its
independent byte equation, retaining the reservation hypothesis. In particular,
audit/status equality is conditional on the byte equation; no fixture instance
of that hypothesis has been proved.

Attempt 36587 rejected an overstrong definitional equality between the whole
fixture-boundary and joined-caller native dictionaries. Its failed output
contains compiler-generated `sorryAx` from elaboration errors and is **not
accepted evidence**. The replacement uses explicit record-field converters;
no whole-dictionary equality is retained.

The explicit replacement `FixtureInputs` checked at 36589 after the local
instance annotation fix diagnosed by 36588. It converts every public/trace/
compilation field and preserves semantic columns. `FixtureSelected.both_source`
checked at 36591: the two canonical fixture selections now inhabit the joined
public caller's ledger source law, with the selector and native instances
explicit. `FixtureData.criterion` checked at 36592 against rw20's independent
serialization model. Its right-hand byte equation and protocol-to-model map
remain open.

Attempt 36590 found missing `PDict_CopyLoop222.olean` through the broad inherited
fixture-family import. The replacement narrows to `DeployedFixtures` and takes
only the exact selector specialization it uses, avoiding unrelated dictionary
transport dependencies. It does not invent a selection or weaken a source law.

**Final combined audit: GREEN, 36599.** It imports the headline and every
PV_Join module and prints axioms for all 126 public PV_Join theorem declarations
plus the headline (127 reports). Six preceding disjoint portions print the full
theorem statements and audit their axioms. All accepted axiom sets are subsets
of `propext`, `Classical.choice`, `Quot.sound`.

| Target | Attempt | Exit | Wall | Peak RSS KiB | Swap | Source revision |
|---|---:|---:|---|---:|---:|---|
| R1Z/PV_Join_FinalAudit (initial) | 36500 | 1 | 0:00.36 | 1279712 | 0 | ce8e0224ab |
| R1Z/PV_Join_FinalAudit (recovered baseline) | 36579 | 0 | 0:03.22 | 4315932 | 0 | 6404c29de5f3c28cc6e9c10931e9ce413e9dd5dc |
| R1Z/PV_Join_CombinedAudit | 36599 | 0 | 0:01.81 | 4335900 | 0 | e97e54529513d8c7c45eab83d83f01c66b00dbb0 |

**Budget exhausted: 100/100 actual host Lean compiles; 96 passed, 4 failed.**
IDs 36500–36599 were used exactly once. The last five attempts were audit
portions/final audit. Peak across all runs: 4,528,716 KiB; swap zero. No failed
source was rerun unchanged. The failures and their replacements are retained
at 36500/36579, 36587/36588/36589, and 36590/36591. The fourth failure is the
instance annotation diagnosed at 36588. The missing dependency in 36590
caused an import narrowing rather than an unrelated dependency rebuild.

This final focused audit is not a clean frozen-manifest release replay.

## Evidence and next deliverable

Every host compile has source snapshot/hash, dependency fingerprint, revision,
target, exit, wall, peak RSS, swap, and full axiom reports in its receipt.
`attempt-tally.json` is the separate 100-attempt allocation with a hard
five-attempt final-audit reserve. No Kani or local Lean compilation was used.
No shipped code, wallet key, sibling worktree, or launcher is changed.

Next: publish/consume the concrete protocol-to-fields/queries/slots model
instance; associate actual compiled transfer inputs first, then withdrawal;
prove their byte equations with execution reachability receipts; derive full
status/audit and V163 equations; establish native successful witnesses.

Continuation commits are in `commits.txt` (the final evidence commit follows).
