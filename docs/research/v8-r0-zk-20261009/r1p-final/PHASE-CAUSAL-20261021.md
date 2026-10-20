# Phase causality work (2026-10-21)

Branch `codex/cx-priv-phase-20261021`, base `f8b9836e0`.
Only new modules are added. BuilderSource/SourceIdentification are untouched.

## Stage 1: symbolic schedule

`R1Z/PhaseScheduleBin.lean` assigns dependency stages to every transcript and
commitment position. Bindings, seeds, both expander streams and salts precede
C1; C2 is between semantic rows 1 and 2; folded is between opening rows 29
and 30. Binary nodes increase by depth, reusing `CausalTreeOrderBin`.
Within a stage an abstract finite equivalence breaks ties. A finite linear
order isomorphism constructs `ord`; proofs use only its order laws. No
concrete position list, `Finset.univ` evaluation, or recurrence is reduced.
Mathlib's generic finite-order isomorphism is internally implemented with
sorting; it is never evaluated here. This is a noncomputable mathematical
order, not an extracted efficient scheduler.

Attempt 9000: exit 0, wall 3.27s, peak RSS 3503544 KiB, swaps 0;
four axioms audits use only propext/Classical.choice/Quot.sound.
Exact source revision/hash, launcher reservation and complete output are in
`phase-attempts-9000-9199.jsonl`. The initial runner fingerprint omitted the
Mathlib import after a failed object-path lookup. The supplemental hash is
recorded separately; a duplicate invocation was refused before compilation.
The runner now fingerprints Mathlib imports correctly and fails immediately
on a dependency lookup or launcher failure. No unchanged compile was repeated.

## Source boundary found during inspection

`BuilderSource.prover` constructs an honest trace builder, not a wire or a
decoder. `WireLengthsR1PBin.Wire` carries arbitrary byte vectors and proves
length facts only. It has no function from `JointView.view` to those vectors.
No existing definition assigning `R1Wire.frame`, `payload`, or `dec` to that
builder was found. `JointView.view` also contains arbitrary `outputs x ch`.
Thus length proofs and the builder relation alone cannot certify phase
dependencies. This must remain explicit in any final source handoff.

## Endpoint disposition

Pending focused development. `PrivacyR1Final.lean` is unchanged.

## Stage 2: dependency refinement interface

`PhaseLocalityBin` defines `R1PhaseWire` with evaluated frame/payload/final
noninterference fields and componentwise `DecodeLocal`; `R1PhaseProver`
carries leaf noninterference and constructs both the shared binary grammar
and symbolic order from the supplied data. The old data's arbitrary caddr
and ord are discarded. `phaseDecode` constructs a block-local decoder and
`phaseDecode_local` proves its component dependencies. This construction
alone proves no sampling law or Rust decoder equality.

Focused attempt 9006 passes (2.37s, 3527080 KiB, zero swap, standard axioms).
9001 failed on a qualified circle-point type name; 9002 passed the initial
interface; 9005 passed the additional decoder contracts. 9006 changes the
prover projection to an abbreviation to expose its position types to Lean's
rewrite transparency. Complete evidence includes all failed diagnostics.
New-module source/object replacements are snapshotted per attempt under
`aspis-joint-20261019/snapshots/codex-cx-priv-phase-20261021/`. No pre-existing
module's shared source or object has been replaced. Dependent targets use
fresh object fingerprints after each dependency change.
