# Exact missing source obligation (working note)

No stable `PV_CB_Op223Source.op223_source` is published yet. No row or endpoint
premise has been removed. This is not a shipped-source counterexample.

The unchanged V164 consumer `ProverRw19CanonicalAuditRefinement.refinement`
retains `P_source_p6`, `P_proof_bytes`, and its reservation equation. The exact
before statement and immutable sibling revision are in RESUME5-V164-BEFORE.json.
For that unchanged consumer, the smallest sufficient source proposition is its
existing function equality:

```lean
ops.op223 = @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)
```

Equivalently this needs pointwise complete-Result agreement for every tag,
slice and lambda in that type. It cannot follow merely from installing the
other arithmetic callbacks: op223 remains an unconstrained independent field.
The previously checked Op223Boundary.no_universal_binding proves this model
boundary; it is not a counterexample to the shipped Rust row.

The bounded P6 route instead needs complete native agreement on the actual
reachable domain, plus proof that the producers remain in that domain. The
length16 array shape is already checked. Numerical canonicality of the tag and
selected sampler is already checked; the draft producer proof tracks canonical
trace reads and limb offsets through all16 returned values. A conditional
input invariant must still be connected to the full shipped producer.
A length16 Kani result alone must not be promoted by funext to unrestricted
function equality. The existing Op223Callsite.endpoint theorem is the domain
transport available for a consumer restricted to proven reachable arguments.
No read-only ProverRw consumer is edited in this worktree.

Extraction and Kani outcomes will be appended after the actual scopes finish.
