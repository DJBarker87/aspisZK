# Rejected-tail inventory for the next source-lowering repair

Static source audit, not a new whole-batch theorem or compiler-bug diagnosis.
Rust candidate.rs:173-206 and retained raw Funs.lean:155-305 are pinned in
BEf_rejection-provenance.json. Existing accepted-only proofs stay within their
original scope. No shipped source, generator or proved module is changed.

| Reached branch | Rust return | Retained emitted pending value | Scratch at emitted branch |
|---|---|---|---|
| Duplicate index, different leaf | Err(Merkle) | some(Err(Merkle)) | current idx,val |
| node_count returns None | Err(Merkle) via ? | none after discarded residual result | current idx,val |
| count exceeds slot capacity | Err(Parse) | none | current idx,val |
| Nonzero padding word | Err(Parse) | none | current idx,val |
| verify_in_place returns false | Err(Merkle) | none | verifier-returned idx1,val2 |

The enclosing emitted tree converts none to outer fail(panic). The correct
source residual must be retained AT THE BRANCH. A final blanket none→Parse
change is not an error-preserving repair: several branches require Merkle.
The verifier-false arm must retain its actual mutated scratch; the padding
frame theorem must not be reused for that different arm. Every previously
issued leaf/parent hash remains part of the rejected prefix.

Concrete validated coverage in this job is nonzero padding. Native R002/R003
reach that branch in the shipped verifier body on a mutated adopted fixture
for both transactions, with10/12 preceding leaf calls. K006/K007 prove the
complete terminal fragment on a singleton-index domain; K009/K012 prove the
exact guard on the actual fixture's counts, and K010/K011 prove those actual
counts in the unchanged multiproof library. Other rows here are source
inspection and retained earlier local Lean evidence, not new Kani checks.

Next concrete deliverable: a new, correctly extracted/referenced batch-tree
pending-return encoding preserving each source error and scratch output;
then local all-Result/effect equivalence checks, source-prefix composition,
and the native mutable-carrier instance for both installed slots. A value
projection or an accepted-only helper must not be relabelled as that result.
