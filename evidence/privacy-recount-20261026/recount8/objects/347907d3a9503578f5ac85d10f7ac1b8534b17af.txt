# V045 native snapshot agreement component — checked

`SnapshotRoot31.checked` (44651) reads the source validation guard. Below the
returned capacity, validation equates the supplied root to reconstruction;
`frame` proves reconstruction ignores that supplied root. RootConstructor31
(44657) extracts validation/bounds from successful constructors. AppendCapacity31
(44667) derives strict nonfullness from constructor validity plus the TreeFull
append guard. The full-tree validator branch is deliberately excluded by this
proved append consequence, not by an extra caller assumption.

LateSnapshot31 (44668) retains the exact empty-root call and the initial-root
read on successful late_append. SnapshotUnique31 (44669) then proves equal index
and frontier imply equal initial roots on any two successful late appends;
records and output leaves may differ. Sequence/index equality is also derived.
All loops/hashes stay symbolic; no hash injectivity or concrete normalization.

CanonicalWordEq31 (44672) proves injectivity of canonical u32-to-field values,
digests and frontiers. SnapshotAgreement31.agree/whole (44674) derive native
snapshot index/frontier/root/sequence agreement from successful inner compiles,
canonical frontiers and equal semantic Public values. Equal pool and deployment
bytes then give equality of the complete native input snapshot. The source
metadata root and sequence are no longer independent equality hypotheses in
this component.

NativeSnapshot31.from_input/actual/caller (44685) read exactly that validated
snapshot from the typed native public value installed by NativeSelectedInputs.
The selected dictionary and caller type dictionaries are explicit and equal to
the existing adapter's. This functional projection does not prove native OS,
memory-erasure or observer equivalence. It adds no trust field.

Retained failures56(syntax),70(field inference),83/84(native dictionary/type
instances) are recorded; only changed sources were recompiled. Earlier native
link evidence retains its structural(K-1 substitute) class, not Kani credit.

## Remaining endpoint work

Full native public agreement still needs the other request/context and output
coordinates connected on the actual public fibre. Semantic Public omits context
bytes; pool/deployment/destination framing stays P work. The new theorem keeps
pool/deployment agreement explicit and derives the snapshot metadata from source
guards. No deployment selector is invented or sought.

V038 complete disclosed/oracle view agreement, all common samples, errors/retries
and visible side channels remain unproved. No complete RustRealRefinement,
native source-body instantiation, endpoint-field removal or privacy conclusion
is inferred from this component. The observer, simulator, failure event and
three-field T cap are unchanged. The privacy target is not yet established.

## Final preflight correction

The typed NativeSnapshot31 adapter compiled at44685, but the expanded final
source-pin check found unmatched sources in NativeSelectedInputs/CallerWorld
dependencies, including an actual AspisR1PublicPreparation.Funs hash mismatch.
Its deployment/source correspondence is therefore unconfirmed; the final audit
excludes this adapter. SnapshotAgreement31 and its constructor/append proofs
are audited independently. The endpoint audit is likewise stopped for this
source-cohort issue. No mismatched object was replaced or rebuilt. The exact
module paths and both hashes are in recovery/endpoint-audit-cache-mismatches.json.
