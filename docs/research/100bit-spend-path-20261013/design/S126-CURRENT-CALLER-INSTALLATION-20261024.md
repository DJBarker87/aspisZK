# Current codec/first and S1 enclosing caller composition, 2026-10-24

Checked source/value progress, not whole S1 or S6 closure. S2 remains with its
new owner. No Rust, frozen production, other session worktree or backend cone
was changed. The <=2^-100 per-attempt target is not yet established.

## Concrete current codec and full carriers

`S6CurrentAdapterCarrierV1` checks bijections for fourteen COMPLETE current
`AdapterRw`/original-native declarations, including every statement, nested
snapshot/frontier/payment field and format-error constructor. No public record,
state carrier, error enum, frontier or validator is simplified. The independent
transition-kind enum absent from the current caller is not needed by these
statement/error carriers. All actual outer encoder tags remain established by
the existing installed encoder source proofs.

`S6CurrentCodecInstallationV1` installs concrete `op22` and `op47` into the
CURRENT complete `AdapterRw.Ops`. The former is the original separately
extracted outer encoder with concrete native children and complete error
transport. The latter instantiates the retained original extracted thin boxed
decoder with the concrete original native decoder on the current carrier.
Its original map_err/try/branch control is retained. `boxed_eq` checks its full
Result, including Rust rejection and outer fail/div. It maps format rejection
to the original InvalidAccountData. There is no free encoder/decoder callback.

`installed_roundtrip ops original statement encoded` has exactly this scope:

```
(install ops).op47 original = ok (.Ok statement) ->
(install ops).op22 statement = ok (.Ok encoded) ->
encoded.val = original.val
```

This is the full quantified body requested by
`S2Y_ForestPublic.FullForestAcceptedRoundtrip`, on the same current complete
statement carrier and concrete codec installation. No independent child
correctness, validity, length or field equality premise remains. The original
named S2Y/S2W consumer dependency closure has not been replayed here, and the
arbitrary ambient AdapterRw.Ops is not claimed to satisfy the law without
this explicit installation.

`S6CurrentCodecTotalV1` proves both codec slots TOTAL in the extraction's value
semantics on arbitrary inputs and derives current accepted inverse from just
that decoder's acceptance. It reuses the original native decoder/encoder
TOTAL results; range/index/cast obligations are discharged there. This does not
prove native Box allocation/abort totality or totality of arbitrary remaining
caller operations.

## One actual extracted owned parent, concrete first, same statement

The complete current `AdapterRwModel` and `AdapterRwCuts` are reused, including
original module names, bodies, account/proof ranges, instruction guards, errors
and release observer None. Module names are retained so these proofs can compose
with current caller imports; a second namespace with merely similar carriers
would not supply this instance.

`S6CurrentStage1CodecJoinV1.accepted_stage1` derives native decoding, the exact
public1880 inverse, original semantic selector, reached proof range, validator
and THIS returned checkpoint from one accepted current owned-stage1 call with
the concrete codec slots. No independently successful checkpoint or child is
an input. Reencoding is a derived mathematical codec fact; it is not inserted
into stage1's actual execution or counted as another runtime operation/query.

`S6CurrentVerifierCarrierV1` checks complete current adapter/verifier public,
nested field, error and phase bijections. `S6CurrentFirstInstallationV1.current`
installs the original current `verifier.candidate.tx1` body in op10. It forwards
the original digest callback and hash state argument unchanged, transports all
observer phases by the checked bijection, preserves all returned errors and
outer fail/div, and retains the exact returned Vec value. The release None maps
to None. `selected_public` proves the current caller's original semantic_public
selects the same full decoded statement's preparation projection, both variants.
`first_decoded_eq` proves full Result equality through the original error
callback, rather than just acceptance equality or an independent continuation.

`S6CurrentStage1FirstJoinV1.accepted_stage1` now establishes:

```
current_owned_stage1 (install adapterOps verifierOps) ... = ok (.Ok cp)
  -> exists reached publicBytes proof split statement encoded,
       concreteDecode publicBytes = ok (.Ok statement)
     & originalNativeDecode publicBytes = ok (.Ok (toNative statement))
     & concreteEncode statement = ok (.Ok encoded)
     & encoded.val = publicBytes.val
     & FirstComposition.firstCurrent InvalidAccountData verifierOps
         actualCurrentSolanaDigest actualErrorMap
         publicBytes proof split = ok (.Ok cp)
```

The proof obtains all arguments from that one parent's reached calls. The
current first/first_decoded/tx1 connection and full-public codec are concrete;
the remaining verifier backend Ops are still explicit. The theorem is about
the extracted current owned caller with these installed source children, not
a proof that arbitrary native SDK execution has this interpretation.

## S1 caller premise actually removed

`S1CurrentOwnedPreparedJoinV1.current_owned_stage1_claim_and_rank` composes that
same enclosing parent with the existing original Prepared.new/borrowed-claim
proof. Before, `first_borrowed_reference_claim_and_rank` required independently
supplied successful `FirstComposition.firstCurrent` execution. After, the sole
execution input is accepted current owned-stage1 with the concrete codec/tx1
and existing preparation installation. Its byte/proof/split arguments and
Solana digest are obtained from that parent; its same checkpoint, semantic,
selected view, prepared values, gamma scratch, canonicality, payload meaning,
reused gamma powers, joint trace under the parameterized sampling/embed
boundary, and post-preparation continuation are derived.

The original preparation theorem's conclusion/quantifiers are retained. Its
previous generic error carrier is specialized to the actual current ProgramError
and error map; its free digest is fixed to the actual installed SolanaDigest
carrier/callback. The bytes/proof/split are existential reached arguments from
the accepted parent. No arbitrary proof/public projection or independently
successful prepare/continuation replaces the original event.

This is caller-premise removal in the CURRENT EXTRACTED SOURCE/VALUE theorem.
It does not discharge the native original prepared_claim vs borrowed-reference
correspondence or instantiate sampling/embed/backend interfaces just because
those interfaces appear as arguments rather than hypotheses.

## Exact remaining obligations and source decision

- Native SDK/account/owned admitted-cut relation, allocations/Box/Vec owners,
  capacity, ordered runtime/oracle observations and rejected fail/div/abort
  prefixes are still required. No inert ghost state or liftValue frame is
  offered as that relation. S2H's stateful Children/public/first ports remain
  separate; this work does not modify or claim closure of that transferred track.
- `adapterOps : AdapterRw.Ops` remains for all fields other than concrete codec
  slots22/47 and installed tx1 slot10. These include SDK/account/hash/error-log
  operations. Forwarding an actual callback preserves its invocation expression
  but does not identify a native runtime/oracle state interpretation.
- `verifierOps : AspisR1CurrentCaller.Ops` retains the nested verifier backend
  interfaces. In the S1 specialization, the existing preparation installation
  supplies original Prepared.new and selected source view, but
  `sampling : PreparedModel.Boundaries` and `embed : M31 -> Result PE`, plus the
  original native prepared_claim/reference correspondence, remain unclosed.
  Other sessions' S3/S4/S5/S9 source instances must be composed at reached inputs.
- The original current S2Y/S2W named consumer needs its focused integration
  replay with this concrete installation; whole-source/release dependency
  closure, runtime binding and final artifact/axioms gates remain required.

No security contract, source adoption or protocol decision is requested here.
The proof-only discriminant naming/import candidate must be integrated and
re-pinned coherently before release. It changes only metadata naming and the
global attribute key, using the original pinned Aeneas generator and original
enum types/tags/readers. It avoids the historical cached prototype's duplicate
builtin attribute registration. It is not a Rust/source behavior change.

## Source identity and validation

Current source snapshot is research b797d6d360b460b527c046e37dad1106e8beeabc.
The full Rust verifier file is byte-equal at b2727acd3abf79315d18b754a260f58f4b1c6326,
historical adopted freeze25866ec331cc7ce27dd9956609c11d32fa8fa58a and this research
revision, SHA256 8c872d42bdaa245cc540be6b26d17108a5cb40754b8befb79e147f5843b1f756.
The first_decoded and thin boxed decoder spans are byte-equal across those
revisions and retained extraction input. Other adapter/program contents changed;
whole-file or compiled-artifact equivalence is NOT inferred. The current
owned-adapter/H5 release authority remains default f8c0ec72... and devnet
63ad3e9c... per the lead handoff, not the old historical ELF pins.

Thirteen focused selected targets passed, one local Lean job at a time under
the atomic lock, -j1 -M4400 and pinned warm imports. Sum selected wall121.904s,
peak RSS3,801,759,744 bytes, zero swaps. Fifty-six printed axiom reports use only
standard propext, Classical.choice and Quot.sound (or no axioms). Exact commands,
source revisions/hashes, original and materialized sources, imports/tool pins,
exit0, wall/RSS/swap and axiom output are in the source-only packet. No binary,
compiled object, unchanged full replay, custom axiom, sorry, native_decide or
resource-option override is distributed/used in accepted source.

Packet prefix: evidence/s126-current-caller-20261021/s126-current-caller-installation-.
Audit: tools/s6-full-forest-roundtrip-20261023/check-current-caller-installation.py.
Materializer and both complete-schema bridge generators support --check.

Excluded attempts are retained separately: old cached naming syntax failed on
the new explicit attribute arguments; the first new naming key collided with
the original prototype on combined import. Renaming only the global attribute
key resolved it. Temporary alternate module names would duplicate original
current declarations in consumer imports; original module names are retained
and the changed-import dependency chain was focused-recompiled. Codec and first
proof attempts exposed alias qualification/projection and whole-Result map/bind
normalization, repaired with explicit source/Result facts, without higher limits.
Failed compiler-recovery sorryAx is not accepted evidence. No failed target was
rerun unchanged; the source/import/key/normalization changes are recorded.
