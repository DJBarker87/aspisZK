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
