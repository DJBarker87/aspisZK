# S1 concrete preparation installation — 2026-10-24

Status: focused proved owned-source value composition. **S1 and S6 remain open;
the ≤2^-100 actual-release target is not established.** S2 ownership remains
transferred. No production code or source-adoption decision changes.

## Exact enclosing result and premise removal

`S1CurrentOwnedClosedJoinV1.current_owned_stage1_closed_claim_and_rank` starts
with one successful `AdapterRw.r1_pool_adapter.owned.stage1_owned` execution,
using the current full AdapterRw carriers and
`AspisS6CurrentFirstInstallation.install adapterOps (closedInstall ops)`.
It concludes the same reached decoded statement, source wide view, semantic
verification call, canonical gamma/kappa, full payload claim meaning, all 29
reused gamma powers, `ExactSerializedRankTrace`, and the actual same
`afterPrepare` continuation/checkpoint with observer `None`.

Before: `S1CurrentOwnedPreparedJoinV1` had explicit arbitrary sampling and
embedding parameters. The stronger intermediate
`S1CurrentOwnedConcreteJoinV1` installs the original serializer and the total
M31 embedding and obtains the serialized trace from the existing concrete
caller theorem. After: `S1CurrentOwnedClosedJoinV1` has neither a sampling nor
an embedding parameter. The accepted parent, quantifiers over account/data
inputs and continuation conclusion are retained; no independent successful
first, preparation, parsing, scratch or continuation premise is introduced.

`S1PreparedActiveBoundariesV1.prepare_eq_of_active` proves full Result/function
equality of scratch preparation given equality of the seven active children.
`concrete_sampling_irrelevant` discharges all seven by definitional equality.
`S1ClosedPreparationInstallationV1.originalNew_sampling_irrelevant` lifts this
to the original Prepared::new transport and `closedInstall_eq` proves complete
Ops equality for every old seed record. The closed record contains defined
existing procedures, including a defined legacy claim field; no dummy diverging
or opaque carrier replaces execution.

Correction to earlier residual-premise reporting: the arbitrary sampling seed
was already overwritten at **every used** field by the concrete installation.
Its retained legacy `sampling.claim` field is never called by scratch
preparation (the separate outer claim child is called). The new equality proof
establishes irrelevance for all outcomes, including rejection/divergence in
the value semantics. Removing the seed is a real interface cleanup, but does
not newly prove that native samplers execute those procedures.

## Remaining premises and scope

The theorem retains `adapterOps`, remaining verifier `ops`, oracle/duplex
parameters and public/root/length inputs, and the successful owned-model parent.
The verifier's original `prepared_claim` native-to-owned reference association
is **not** established by this result. Nor does it discharge the actual SDK
account borrow/state frame, allocation failures, aborts or ordered runtime
effects. Other cone backends remain their owners' obligations. No unproved
native source refinement is relabelled as a cryptographic assumption.

The full statements are in
`lean-candidates/s126-caller-boundary-20261021/S1CurrentOwnedConcreteJoinV1.lean`,
`S1PreparedActiveBoundariesV1.lean`, `S1ClosedPreparationInstallationV1.lean`,
and `S1CurrentOwnedClosedJoinV1.lean`.

## Validation and pins

Four smallest changed targets were compiled individually against the pinned
warm import closure, with `lake env lean -j1 -M4400` and the shared atomic
local lock. All exited zero: summed wall time 90.212027 seconds, maximum RSS
3,794,616,320 bytes, zero swap. Eleven `#print axioms` reports contain only
`propext`, `Classical.choice`, `Quot.sound` (or no axioms).

`evidence/s126-current-caller-20261021/s1-closed-preparation-targets.json`
selects the exact four receipts; the associated `-import-pins.json`,
`-tool-pins.json` and `-reused-pins.json` retain source/tool/dependency hashes.
Receipt source revision is parent `71c9ec31e5bdc8951708eda92169419ee619112c`;
the changed source hashes, rather than that parent alone, identify the tested
files. No compiled object is distributed. This is focused cached validation,
not a coherent final release replay.

Run `python3 tools/s6-full-forest-roundtrip-20261023/check-closed-preparation.py`
to audit the packet. Existing source-freeze/source-installation pins remain in
`S126-CURRENT-CALLER-INSTALLATION-20261024.md` and its referenced packet.

Next deliverable: a checked original native claim-to-owned execution connection
with concrete leaf association and error/totality transport, then composition
through the actual SDK frame supplied by the transferred S2 track.
