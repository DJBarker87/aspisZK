# D542 continuation record

Baseline `80a46315746a17a9511b32ca331d262811c65c08`, same worktree and
`codex/pv-evh-20261029`. No delegation, push, extraction, native run, Kani,
wallet operation, frozen source edit, or other worktree write.

## Accepted source progress

- 73661, `PV_EVH_DurableWithAttempt.run_fixed`: source-specialized durable
  reserve-and-build installed into with-attempt, retaining its ten other
  leaves and the eighteen with-attempt leaves. No universal nonce-store
  premise is needed at this actual-store use.
- 73663, `PV_EVH_AccountGuard.retrying_fixed` and `entry_fixed`: the entire
  op233/trait-default comparison is an explicit unfinished Prefix callee,
  rather than an apparently effect-complete Result lift.
- 73664, `PV_EVH_DurableProver.entry_fixed`: the above actual-store
  source interpretation composes through masked attempt and proof-account
  entry. Native file events from the inherited nonce interpreter survive.
  Account acquisition, entropy helper coverage, native leaf laws and the
  comparison remain open. This is local source Result transport only.
- 73672, `PV_EVH_SliceBind.pure_bind_fixed`: axiom-free pure bind normalization.
  It handles only a language-level pure value, with no allocator or external
  interpretation hidden inside it.

All exact target, source revision/blob/hash, object/dependency fingerprint,
exit, wall time, peak RSS, swap and axioms are in their receipt-ID.json files.
Accepted axioms are subsets of propext, Classical.choice, Quot.sound.

## Failure replacements

73660 left generic store instance identifiers in emitted closure arguments;
73661 substitutes the exact actual instance. 73662 omitted the newly named
comparison compatibility in one entry proof call; 73663 threads it explicitly.

73665 exposed formerly lifted entropy helpers but omitted the ControlFlow
constructor namespace. 73666 fixes the namespace and isolates a tuple-bind
unification failure. 73667 and 73668 try increasingly explicit normalization
of the tuple pattern but do not solve it. 73669 fixes source Results at all
binds, making source dictionary inference fail earlier; 73670 limits that
constraint to pure conversions, retaining the original tuple obstruction.
73671 specifies the full source continuation and fails elaboration (an
unconstrained record literal), then reaches the ordinary heartbeat limit.
No memory cap or heartbeat limit was raised. Its replacement is the small
symbolic pure-bind lemma (73672), followed by a generated use at each pure
mutable-slice conversion. Candidate 73673 is staged with that changed source.
It must not be mistaken for an accepted proof while admission is refused.

## Prepared, not yet validated

EntropyStep/EntropyFlow and the AccountFlow/AccountFlowEntry/DurableFlow
composition expose entropy helpers and restoration functions. NoncePath,
SyncDirectory/NonceReserveFallible/NonceReserve/NonceReserveBuild expose the
nonce helper cone while retaining typed native file handlers. MaterialFromEntropy,
ApplyMaterial, BuildSemantics, ProveSemantics and PrivateSalts expose further
prover source spines. Uncompiled modules earn no proof or native coverage credit.

Every generator has --check; audit.py checks the byte identity of these drafts
as well as all accepted source/receipt/object evidence. The source-reference
census is textual only (628 declarations, 255 external aliases); dictionaries
and callbacks can add edges. It is not a native coverage or fidelity theorem.

## Acceptance status

Rows removed: NONE. Target not yet established. Complete native coverage,
NativeTrace projection links, runjoin opsNative/allocator installation and
successful actual-domain nonemptiness are still open. No (v') reduction is
claimed. No final axioms audit or release replay has been consumed.

The changed 73673 candidate was eventually admitted after four full-cooldown
refusals. Pure bind normalization solved the tuple-restoration obstruction;
the remaining failure was a Boolean guard simplified to `false = true`.
73674 adds the exact Boolean equality normalization and PASSES
`PV_EVH_EntropyStep.run_fixed` (wall 0:07.18, RSS 2,643,800 KiB, swaps 0,
standard axioms). Seven helper interpretations are explicit and preserve all
restoration functions; none is a whole afterDraw answer. Their actual native
semantics/fidelity remain OPEN. EntropyFlow is the next dependent bridge.

73675 was admitted after two further cooldown refusals and failed only on the
source loop equation's symbolic Result/control-flow match. 73676 case-splits
that value and PASSES EntropyFlow. AccountFlow 73677, AccountFlowEntry 73678,
and DurableFlow 73679 PASS. `PV_EVH_DurableFlow.entry_fixed` is now the most
composed accepted entry transport, using the expanded entropy helpers and the
actual-store reservation interpreter. The original Result-only afterDraw is
not used on this new path. It still uses the inherited nonce helper interpreter
and retains native effects/adequacy and comparison/account inputs as OPEN.

73680 NoncePath failed because a source binder `(P : Type)` shadowed the Prefix
monad alias. The changed generator qualifies that carrier on nonce modules;
73681 is the next candidate (currently admission-refused, not launched).
The fallible-reserve generator also handles its source pure conditional bind
symbolically before any launch, following the already accepted old nonce proof
shape. No source recurrence or concrete SHA computation is normalized.
