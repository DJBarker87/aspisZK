# Native premise-family audit

Base: d385c8908f, branch codex/pv-srcid2-20261026. Target not yet established.
The exact five fields, in requested order (unchanged):

```lean
  compile_call : ∀ i, run (inputs i) = ok (.Ok (inputs i).compiled)
  words : ∀ i records, newRecords (inputs i) = ok records →
    WitnessOk (wordWitness records.w)
  publicCorr : ∀ i records, newRecords (inputs i) = ok records →
    PubCorr (wordPublic records.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
  admission : ∀ i records, newRecords (inputs i) = ok records →
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w)))
  row_call : ∀ j, transport j = PV_Src_Transport.row j

```

## compile_call

Before = after: the field above, including both Result layers.
Classification: OPEN pure callee-success obligation, plus selection of valid
inputs and the actual returned payload at the caller boundary. D188 applies to
the extracted compiler; it does not supply implementations of Records.call
and ExternalLinear.call. These are explicit uninterpreted dictionary fields
in BuilderForestAdmissionPort (lines 4362 and 1865). They are not effects.
No reduction or premise discharge is claimed at this stage.

The canonical stage certificate uses encoded records directly. It does not
construct a successful native compiler execution for either release fixture.
Reusing that certificate as compile_call would change the statement.

| Family | Before fields | After fields | Status |
|---|---:|---:|---|
| compile_call | 5 | 5 | OPEN: actual callee/reference implementations and valid-input run proof |

No new Lean theorem is asserted in this commit; no compile receipt is claimed.

## words

Before = after: `∀ i records, newRecords (inputs i) = ok records →
WitnessOk (wordWitness records.w)` (full field above).

Classification: not an unconditional pure mapper law on this Input carrier.
The shipped mapper copies `out` into `RW.output_value` (Rust lines 249–252),
without testing the 30-bit range. `WitnessOk.values` requires all three values
strictly below `2^30` (R0Z/BuilderWitness.lean). The extracted owned reference
has the same issue: `PV_Src_RecordRangeObstruction.reference_counterexample`
constructs a successful return with output `1073741824#u32` and proves that
WitnessOk fails. Attempt 25000 checks it, using only standard axioms.
This theorem alone is not shipped/reference P6 equivalence.

The selected-input interface must establish, for every installed `i`,
`(inputs i).witness.pair.value.val < 2^30`,
`(outputValue (inputs i).request).val < 2^30`,
`(inputs i).change.value.val < 2^30`, canonical first/second pair commitments,
20 canonical membership siblings and 3 canonical super-root siblings.
The computed bits are intrinsically Boolean (existing NativeDirections),
so Booleanity needs no new caller assumption. Source validators are relevant:
`BuilderAdmissionRecords.words_of_common_success` is already available for
its extracted reference carrier. The missing outer-caller selection and
successful validator interpretation belong at the pv-runjoin5 interface;
the unstubbed full mapper P6 association is still a pure OPEN sub-obligation.
Do not classify this omitted pure callee implementation as an OS effect.

| Family | Before fields | After fields | Status |
|---|---:|---:|---|
| words | 5 | 5 | OPEN; reference obstruction proved, shipped check pending; needs selected-input validation |

Neither canonical release fibre has been removed or restricted. No native
fixture inhabitance or premise removal follows from the obstruction theorem.

## publicCorr

Before = after: the seven-field `PubCorr` conclusion printed above, for the
record returned by `newRecords (inputs i)` and the public projection taken
from `(inputs i).compiled.public_statement`.

Classification: native association of the installed caller's selected input,
snapshot and returned compilation. The missing pv-runjoin5 interface must
identify the request variant and asset, and the constructor's snapshot index
and frontier with the returned compilation's live snapshot. In addition the
source mapper/root implementation must supply the canonical twenty empty roots
and canonical snapshot frontier. The exact required conclusion is:

```lean
∀ i records, newRecords (inputs i) = ok records →
  PubCorr (wordPublic records.p)
    (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
```

`PubCorr` expands to variant, asset, next, frontier, empty, frontierCanon,
emptyCanon. An arbitrary `Input` can store a compiled snapshot unrelated to
its constructor snapshot; mapper semantics alone cannot establish `next`.
D188 does not identify two unrelated pieces of supplied data. This is a
caller interface, not a new extraction-trust requirement. Stop this family
at the named interface; no source discharge claimed.

| Family | Before fields | After fields | Status |
|---|---:|---:|---|
| publicCorr | 5 | 5 | REDUCED to the exact seven-field selected-record/returned-public interface above; unchanged obligation |

## admission

Before = after: `∀ i records, newRecords (inputs i) = ok records →
BuilderSpendRelation.RspendPlus (mapPub (PV_Src_Public.canonicalPublic
(publicInput (inputs i)))) (BuilderCanonical.liftWitness
(BuilderRecordCanonical.witness (wordWitness records.w)))`.

Classification: native association of the deployed caller's admitted input
fibre with the semantic witness and public statement. The exact missing
pv-runjoin5 interface is the statement above on the installed `inputs` family,
with the same record as its successful constructor call. It must carry the
original `Rspend` conjunction and the transfer-only nonzero change limb-7
sentinel; it cannot be weakened to value bounds or successful bank generation.
The raw mapper does not validate conservation, Merkle membership, nullifier,
append transitions, or the sentinel. A successful constructor has no such
postcondition. Outer selected entry validation and the original relation
transport must supply these facts. No assumption of `RspendPlus` is inserted
into a source data definition or relabelled as a pure theorem.

| Family | Before fields | After fields | Status |
|---|---:|---:|---|
| admission | 5 | 5 | REDUCED to exact selected-input RspendPlus interface above; unchanged obligation |

Stop this family at the owned native interface. Both original fixture fibres
remain available without changing their relation, public fields or handles.

## row_call

Before = after: `∀ j, transport j = PV_Src_Transport.row j`.

Classification: native association of the transport actually installed by the
caller. The exact pv-runjoin5 interface is pointwise equality of that selected
`Fin 1024 ≃ Fin 1024` to the row returned by the arithmetic S2 reference, with
all 1024 positions quantified. The already-proved
`PV_Src_Transport.row_eq` supplies `row j = AspisR1.row j` and the existing
unstubbed S2 P6 callee receipt is independently pinned in the predecessor's
`transport-reuse.json`. Neither chooses the caller's `transport` parameter.
Choosing the reference equivalence as the source definition and calling the
field reflexive would not establish which transport the deployed caller uses.

| Family | Before fields | After fields | Status |
|---|---:|---:|---|
| row_call | 5 | 5 | REDUCED to exact installed-transport pointwise interface above; unchanged obligation |

Stop this family at this interface. No new Kani row check is needed for the
unchanged callee, and no historical timeout is rerun.

## Final words disposition (supersedes the pending entry above)

`PV_Src_RecordReference` preserves every nominal record field and invokes the
already-extracted owned function. Attempt 25002 proves `newRecords_eq` and
`words` with standard axioms: for this *reference* dictionary, `Checked i`
(the five primitive input-validation groups printed in attempt 25003) entails
WitnessOk for every successful returned record, for either request variant.
The dictionary is explicitly named `withRoots` and is never globally installed.
It accepts the root table as data. This does not prove the actual root helper
or the unstubbed full mapper equality. No native premise is replaced by Checked.

The actual-source Rust diagnostic imports four immutable shipped `.rs` files
by `#[path]`, including the private root helper's original module and its hash
implementation. It does not duplicate, edit or stub their function bodies.
`srcid2-native3` exits 0 in release mode and checks that `CopyRecords::new`
and `banks()` succeed at out=1073741824, and that merged column 10 row 1010
contains that exact raw output value. The source writer documents/implements
that raw-output cell. Source import and dependency hashes match the worktree
(`source-pins.json`). This is a finite checked source-domain counterexample,
not a Kani proof, shipped-binary association, successful full entry wrapper,
or a counterexample on a valid transfer/withdrawal release fixture.

Two unstubbed full-call Kani checks timed out at 240s, including a separately
identified MIR-optimization diagnostic. Neither establishes this counterexample
nor supplies P6 equivalence. The first intended verification command failed on
a jobs/output-format conflict; its queue was stopped immediately. The diagnostic
was corrected before issuing one fresh command. Every exact harness name was
read from generated metadata before attempting verification; selected stubs and
verified_stubs are both empty. Inventory failures are retained, not evidence.

| Family | Before | After | Final status |
|---|---|---|---|
| words | exact field above | identical field | OPEN: actual mapper P6 equality and selected-input Checked interface; unconditional raw-callee discharge refuted |

No source-to-model field or native endpoint row was removed. The five native
families remain `compile_call`, `words`, `publicCorr`, `admission`, `row_call`:
**5 before, 5 after**. No smaller native instance is claimed. The original
consumer is rechecked in 25003, along with both canonical fixture fibres;
full native fixture inhabitance remains OPEN. The fixed consumer theorem
still selects BuilderSource.prover and accepts no source certificate parameter.
Changing that fact would require the owner of the deployed RunJoin installation.

The REDUCED labels above describe exact remaining native interfaces already
present at the base, not new premise-removal progress by this branch. In
particular publicCorr also has pure mapper/empty-root sub-obligations; those
stay OPEN and are not dismissed as effects under D188.
