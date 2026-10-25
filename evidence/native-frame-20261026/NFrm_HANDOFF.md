# Native frame handoff

S2 OPEN; target not yet established. Branch `codex/cx-native-frame-20261026`.
No ledger premise was removed. No push.

## Exact checked claim

`lean/NFrm_TrustScope.lean` checks an interface obstruction, not Rust behavior.
`reserve_frame_not_from_slots` and `box_contents_not_from_slots` exhibit
well-typed, returning Claims slots that erase contents.
`copy_allocator_nonvacuity` supplies the exact existing copy specification,
its TrustedStd proof, a returning private Unit allocator, and returning slots
violating both content laws. `no_uniform_reduction` proves that the copy trust
record cannot establish those laws for arbitrary Claims slots.
These are deliberately INVALID native-std interpretations, not counterexamples
against shipped source. They are not installed in the accepted-pair theorem.

The check does NOT prove that an accepted Claims output has incorrect rows,
that content preservation is needed as an independent accepted-run premise,
or that the full accepted-pair hypotheses admit the erasing dictionary.
Acceptance already constrains reached value results and the parent overwrites
all three rows. The countermodel only establishes the narrower trust-interface
non-entailment. Native ownership/abort/effects are not expressed by these value
slots in the first place.

## Before and after statements

Before and after: `AspisR1.T2Nat_NativePair.accepted_pair_unified` in
`lean/T2Nat_NativePair.lean` is byte-identical; hash in NFrm_source-pins.json.
Its quantifiers, fixed f/s/cuts, conclusions, acceptance restrictions,
cryptographic hypotheses, oracle model and failure events are unchanged.
There is no strengthened joint top or actual-run native-frame theorem.
The new independent negative statement is exactly `no_uniform_reduction`,
NOT a replacement for that joint top.

## Ledger delta

| Row | Before | After |
|---|---|---|
| L174 initial/pending native instance | Open native Copy/Std/allocator/runtime interpretation | OPEN; no discharge |
| L177 Claims native std slots | Open reserve/intoBox/mapError/boxArray native ownership/abort/effects | OPEN; exact missing primitive trust content isolated |
| L179 library/native frame | Open native std/runtime/ABI/source dictionary association | OPEN; no discharge |

Removed rows: **0**. Added rows: **0**. Added or widened trust items: **0**.
Global ledger deliberately unedited under prefix-only scope.

## Trust-scope stop and recommendation

The exact existing interfaces, printed in NFrm_001/stdout.log, are:

- S2W_TrustedStd: copy_from_slice alone; explicit ambient/private-state frame.
- Port1_Library.TrustedStd: Option::ok_or and Result::unwrap32 alone.
- Allocator: allocate/cleanup on private A, with NO link to Claims reserve,
  Vec capacity/content, intoBox, or an ordered external-effect interpretation.
- RuntimeEntrypointAdmission: initial account/cell/borrow eligibility and SDK
  relatedness; its source explicitly excludes native interpretation.
- RuntimeSyscall: successful hash return values; no std-carrier association.
- D188 extraction: owned stage1/stage2 and digestSource; not a native Claims
  allocator/Box representation contract.

To supply the native Vec/Box behavior by EXTERNAL TRUST through these exact
fields would require additional primitive trust content: native reserve result
association, ownership transfer on intoBox, and private-allocation/abort/effect
interpretation at those calls. Labelling that a specialization of the existing
copy field would widen its stated domain. No such field was added. This is the
explicit no-new-trust/no-widening stop exception, not budget exhaustion.
It is not a theorem that every possible source-verification route needs new
trust: an independently checked primitive/source bridge may avoid it.

Recommendation: retain all three rows. The lead should identify a pre-existing
accepted Vec/Box primitive specification and its exact scope, if one exists,
or obtain concrete primitive/source proofs under existing P6. Do not accept
a generic success/content wrapper or expand copy/runtime admission silently.

There is also an independent OWN-SOURCE obligation: shipped
`crates/aspis-r1-cost-probe/src/r1_semantic.rs:42` uses heap::uninit,
MaybeUninit, three pointer writes, and assume_init. The selected emitted
ClaimsUnrolledParentSource body is `candidate_claims.claims`, using filled(3),
intoBox, boxArray, and delayed setters. std-library trust cannot establish
equivalence of these caller bodies. That source/refinement gap remains a
PROOF obligation, not a proposed trust item or a shipped bug. The maintained
ClaimsUnrolledFinish header already labels native correspondence/adoption open.
Source hashes are retained in NFrm_source-pins.json.

## Non-vacuity and success conditioning

The local countermodel returns successfully from reserve and intoBox; its
allocator both allocates and cleans up successfully. The copy law is inhabited
by specification_satisfies. No impossible accepted spend is assumed. This
is local interface non-vacuity, not a joint deployed accepted-spend fixture.

The old joint theorem remains conditioned on its original accepted wrapper
equations. No new accepted-only source equality, rejected-prefix accounting,
full native Result/log law, or outer-failure/divergence transport is claimed.
The local content laws quantify only over successful primitive returns; even
those laws are not derivable for arbitrary slots from the copy law.

## Validation and budget

1/100 Lean attempts including dependency builds; 0/30 Kani. No missing module
was built. NFrm_001: target NFrm_TrustScope.lean, exit0, wall1.928091563s,
peakRSS4372680KiB, swaps0, source revision79877901a2 plus exact dirty-source
SHA/snapshot in receipt. All four new theorem axioms were printed: subsets
of [propext, Classical.choice, Quot.sound] only. Raw logs and exact source,
command, selected dependency hashes, compiler hash and cgroup limits are
in NFrm_001/receipt.json, stdout.log and time.log.

Retained coherent SInt2 workspace and objects were reused unchanged. The
existing S2W launcher ran lake env lean -j1 -M7000 -DElab.async=false in a
distinct verified systemd scope MemoryHigh6G/MemoryMax8G/MemorySwapMax0/
TasksMax64. Preflight showed init.scope and one RawJ scope; at most16GiB
combined configured reservation with this job, below55GiB safe host budget.
No cap increase, timeout, kill, unchanged rerun, package or manifest replay.
This is a focused cached proof, not a frozen-release rebuild.

No shipped/cfg(kani) source, other prefix, Session A live worktree, wallet/key,
parameter, feature or wire format changed. No Rust/Kani/SBF rebuild trigger.
Inherited ELF hashes, NOT freshly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Only prefix-scoped Lean/evidence files were committed. All stages local.
