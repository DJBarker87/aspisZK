Stage 1 reuses only these reviewed files from parked candidate
`1dfbd5711684d73fc2ff664cfae9ae78f7dd34f8` (not a branch merge):
`Client64_{proof_accounts,inventory,test_proof_accounts,test_inventory}.py`,
`r1_devnet_{spend,inventory}.py`, planner `plan.rs`, and `Client64_accounts.rs`.
The added Rust route test is local work. The first optimized host test failed
because its `prover::` substring also matched `aspis_prover::`, not because
Generic96 remained reachable. Replacement checks use token boundaries and
explicit alternative API names. That failed receipt is retained as unit-01.

31 local Python tests pass (`lifecycle-tests.log`, exit 0, test runner wall
0.651 s; this small local run did not measure RSS/swap and is not a formal
release receipt). The runtime tests below carry capped host resource receipts.
No wallet secrets were accessed by these mock lifecycle tests.

The new ABI validates eight nonzero distinct keys before statement processing.
It rejects legacy independent publication keys, maps successful `attempts - 1`
to both instruction positions, and retains rejected/unentered keys. Existing
selected adapter entropy/semantic/rejection precedence and ledger code are
unchanged; there is no Generic96 fallback. Ready/entered/failed/success manifests
and the exclusive invocation claim prevent automatic retry after ambiguity.
No generic theorem, error-origin erasure, witness-independent nonce-policy law
or complete L1 event-producer refinement is inferred from these tests.
