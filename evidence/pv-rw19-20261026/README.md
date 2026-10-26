# pv-rw19 continuation

Base: `d1351e0a2741079b6e206bfe2d84a0cd70706a3d` on
`codex/cx-prover-rw-20261023`. Env-J allocation 27700–27999;
Lean budget 100, Kani budget 20. No attempt charged yet.

## Gate and classification

LEAD RULING (f) applies from the start: no host scope and no local Lean
compile until the restoration flag exists. Read-only host inventory is not
a compile, extraction, Kani run, or resource admission. Draft Lean is not
checked evidence and is excluded from the rw18 frozen component manifest.
No release replay, axioms audit, or premise removal is claimed here.

## Stage 1: concrete P6 context identity draft

The sibling `codex/pv-cb3-20261026` at
`40361dbd95a58a15c13e9071f752559afddb8dc3` contains no `op223` match in
`PV_CB3_*.lean`. Its exact retained obstruction is copied as
`sibling-op223-obstruction.json`, classified as reused evidence.
There is no available sibling theorem to consume for `source_law`.

`ProverRw19P6ContextIdentity.identity` supplies the context identity for the
**concrete previously extracted owned P6 reference** by functional
extensionality and `ProverRw18ContextReference.compress`. The Rust reference
is `tools/prover-rw-20261023/success-p6/proof/lib.rs:compress`; its indexed
loop terminates at the slice length, and `PV_CompressModel.loop` supplies
the existing arbitrary-slice finite-loop proof. It is not the original
whole-helper extraction. No stubs or new source implementation are added.

`ProverRw19P6Join.callback` and `.dictionaries` consume that identity. They
retain the exact named obligation:

```lean
P_source_p6 : ops.op223 =
  @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)
```

This is an open source-to-reference law. No Kani result currently supplies
it. A finite arity16 Kani check by itself cannot establish this unrestricted
function equality. Existing rw18 and sibling statements stay unchanged.

V164 before: arbitrary `extracted`, `source_law : ops.op223 = extracted`,
`context_identity : extracted = context.compress selected`.
V164 checked after: **unchanged** pending compile. The draft P6 consumer
replaces the arbitrary extraction with the concrete P6 extraction and has
only `P_source_p6`; it does not close V164 or the deployment endpoint.

V163 before and checked after: **OPEN**, with the concrete mathematical
whole-model instance and both proof-byte/audit equations still missing.
The component compression model is not substituted for the whole model.

Next validation, once authorized by the flag: compile the identity module
first, then the join, then dependent callers; retain full target/exit/wall/
RSS/swap/revision/axioms receipts. Never re-freeze a manifest containing
unchecked drafts.

## Stage 2: audit-value reduction draft

The emitted `ProverRwBodyStoreSource.afterReserve` checks the C1 count is
16, the mask-only count is 10, and the d/g/padding flags are true before
returning a successful pair. Its return sets the final total flag to true.
This motivates an independent mathematical constant
`ProverRw19AuditValue.canonical = (16,10,true,true,true,true)`.

`ProverRw19AuditSource.continuation` and `.body` are draft proofs that
every successful source return has exactly that audit, for arbitrary
primitive Results. They preserve all rejection, failure and divergence
cases rather than postulating successful execution. The proof follows only
the emitted body's binds/branches and final guards; it does not normalize
any trace, finite field recurrence, or concrete release fixture.

`ProverRw19AuditData.attachAudit` attaches this audit to an independently
specified mathematical byte-result, carrying error/failure/divergence
unchanged. It is **only a codec**, not the concrete V163 model. Its input
is not defined as the actual source observation.

`audit_of_bytes` derives the complete audit observation equation from
the byte observation equation and the canonical successful-audit invariant.
`ProverRw19AuditCaller` applies this to the body; the conditional
`ProverRw19CanonicalAuditRefinement.refinement` retains exactly:

```lean
P_source_p6 : ops.op223 =
  @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)

reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after)

P_proof_bytes : PV_RW_DataProduct.observe PV_RW_DataProduct.first
  (ProverRwBodyDataCriterion.data
    (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
      store pub compiled v hash binding digest attempt s)) = modelBytes
```

The mathematical whole-model byte function `modelBytes` still has to be
constructed for the deployed caller's admitted inputs and associated with
the mathematical protocol. It remains a parameter of this conditional
consumer. No equality is proved on either whole release fixture yet.
No source-output alias or structure of assumed equations is introduced.

All Stage 2 results remain **unchecked drafts**, so the checked V163/V164
before/after status is unchanged. The lexical preflight only checks forbidden
tokens and the presence of `#print axioms` commands; it is not an axioms
audit or type-check. No attempt IDs were consumed by these edits.

Focused validation order when the gate opens:

1. `ProverRw19P6ContextIdentity`, then `ProverRw19P6Join`, then `ProverRw19P6Caller`.
2. `ProverRw19AuditValue`, then `ProverRw19AuditSource` and `ProverRw19AuditData`
   (sequential host scopes), then `ProverRw19AuditCaller`.
3. `ProverRw19CanonicalAuditRefinement`, then `ProverRw19P6DataIff`.
4. Only after focused targets are green, one final axioms audit and component
   manifest re-freeze/replay. No unchecked source enters a frozen manifest.
