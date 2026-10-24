# Port14LOCAL callback boundary decision

Source: base `5c9969ef912a1e90aaa31f142310f774b6619c3b`, branch
`codex/cx-port14local-20261024`. Inspection only; no new kernel result.

## Decision

Stop the proposed callback-producer proof campaign as mathematically redundant
for `Port13GATE_Authenticated.accepted`. Do not turn witness specialization into
a source-adoption claim. The theorem's actual `sourceAccepted` Program and entire
existential/recovery conclusion contain **no** occupied/sibling/leaf callback.
These parameters occur only in proof comparisons. Set both parents to
`fun left right => .ask (MultiproofConePhysicalDigest.parts left right) .done`
and leaf to `MultiproofConeP6Batch.referenceLeaf`. For every H the two ParentGates
reduce to eval of one ask; LeafGate reduces to reflexivity for every parsed p,
q, natural kind/pos and scratch with n<16. These witnesses are independent of H.
No native totality or success on an unexecuted input follows or is needed.
A wrapper eliminating these witness arguments would add no source theorem.
It is deliberately not implemented or charged as progress.

## Exact entry and already established source claims

| Entry | What the source proof already does | What the callback does |
|---|---|---|
| Port10AUTH_Node.accepted | From actual `erase D hash (Port9OR_P6Node.node ...)=ok out` and per-success `Oracle D hash H`, proves complete ordered trace equals the physical node eval. `Port10AUTH_Total.accepted` derives all reached read successes. | Port10AUTH_Tail compares that physical node with `nodeWith`; its two ParentGates merely replace the comparison's parent asks. |
| Port10AUTH_Leaf.accepted_trace / Selected.iteration | Active actual key/opening reads; exact 832-byte view; derives digest success from the executed iteration; exact address and posthash Result, including conflicting duplicate rejection. | Port10AUTH_Leaves already proves the referenceLeaf fold from physical iterations. Port10AUTH_Tree then uses `leaves_eq` to change that comparison witness to any leaf satisfying LeafGate. |
| Port10AUTH_Tree / Installed.accepted | Composes native keys, sort, reached leaves, terminal count/padding/P6, roots and both scratch arrays; Port9 response-driven interpretation supplies Oracle, not a native-D totality law. | Occupied/sibling/leaf occur in the LHS comparison Program only. |
| P6Callbacks.nodeWith / P6Batch.batch_tree | Physical node continuation checks division, idx update, val update, w+1; leaf ask precedes leaf_step dedup/write; early failures stop. | Gate equality is consumed at these local continuations; no whole-batch conclusion is a gate field. |
| P6Frozen2Stage / Port13GATE_Canonical | Scratch-threaded three-slot sequence; accepted comparison to frozen batch using proof-only total Unit dictionary. | Binary callback is unused by actual nodeWith; occupied supplies that comparison field. |

Port9OR_Code.program is the actual reusable effect producer: fixed before H,
branches on D's existing ok/fail/div policy, asks only on ok, passes the actual
reply to the continuation. `correspondence` retains prefixes even at later outer
failure. `Port9OR_P6Node.parent_source/node_source` identify its erased Results
with extracted reference.write_parent/binary_step; `node_value` is all-H.
Port4B_LeafCode.code_exact/address identify pure ranges, exact parts and one read;
Port4B_NativeLeaf.active/step and LeafStep.reference_post identify actual posthash
control. None needs duplicating.

Parent preimage: three components `[BINARY_NODE_TAG]`, left[32], right[32],
flattened in that order (65 bytes). Source occupied accesses index,index+1;
supplied sibling order follows the physical parity branch. Leaf components:
`[16,113] || opening[0:480] || opening[608:640]`,
`[16,241] || opening[480:608] || opening[640:672]`, or
`[16,114] || opening[672:800] || opening[800:832]`.
Salt is checked before value extraction; digest occurs before dedup, then checked
scratch writes. Port10 preserves the ordered hash before rejected duplicates.

## Unsupported adoption boundary and false stronger targets

`Port4B_Install.leaves` fixes op6 to LeafCode.native and op10 to
VerifyInstall.verify, which calls extracted `reference.verify_owned`. This is a
named P6 source/control/library interpretation, not a fresh extraction of shipped
`candidate::batch_tree` or `multiproof::verify_in_place`. Historical local Kani
callback certificates are external evidence, not Lean proof terms for adoption.
The committed P6-CERTIFICATES.md explicitly preserves this distinction.
Association of actual platform primitive / shipped source with that interpretation
remains the primitive/adoption frontier; do not duplicate Session A work.

A literal all-input full ParentGate for the existing failure-preserving producer
is false: choose D.digest always `.fail .panic`. Port9 emits no ask and returns
failure; ParentGate requires a singleton read and a Digest (its Parent type has
no Result). A successful ask followed by an out-of-bounds scratch write likewise
retains the read and an outer failure; digest-only equality loses that prefix.
Accepted local refinement is sufficient here and already exists in Port10.

No premise, quantifier, carrier, failure event, oracle law or conclusion is
changed in this job. Full existing Port13 statement and expanded hidden gates
are retained by hash/source references in the audit packet. Before=after.

## Independent next deliverable

Choose **full-driver executed-call partition and delegated budget**, not another
comparison wrapper. Reuse Port12COUNT's actual all-outcome 477/3/3/563 bounds,
but never identify its checkpointChain projection with Port1_Driver.stages.
The next design will specify each concrete delegated producer, all-outcome
weights, exact source control multiplicities and the missing <=115 sum.
Unrestricted rest can ask arbitrarily many times at the first op3, so neither
1161 nor a finite delegated budget follows from the current interface.
Parser/prepare7/powers17/sampler/primitive implementations remain Session A's.
StoredCarrierBinding and accepted-source terminal/classifier/no-hit producers
remain separate; authentication recovery alone establishes none of them.

No shipped, protocol, trust, security-contract, key, or ELF change. Both deployed
targets not yet established. Exact bound unchanged:
`(Q+34)*B+kappa(Q+1161)+2^-126+2^-454`.
