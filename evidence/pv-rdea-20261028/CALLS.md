# Deployed callers and argument provenance

Revision: candidate `3e77ed7b62` plus proof/evidence-only commits. Deployed client:
`tools/r1-cost-probe`, binary `devnet_spend`, features
`r1p-check,aspis-r1-cost-probe/ct-host-prover`, rustc 1.94.1, release opt3,
debug assertions/overflow checks off. The inherited complete 487-unit resolved
feature graph is `../pv-rdb1-20261028/resolved-features.json`, SHA256
`613c405ef941cc940fd003ece28b23d910d327e02e19a9f7945bf2b939858f73`.
No extraction, Rust build, Kani run or ELF change is performed here.

## Exact existing row-model call sites

The script checks that ProverRwFullFuns contains precisely one call each to
String.with_capacity and Path.join. These are V181/op30 and V178/op26. This
is a complete inventory of these two calls in that source model, not a
claim of a complete transitive call graph of the deployed executable.

`plan::prove` -> `RealR1_client::prove_for_proof_accounts` ->
`prover::prove_masked_retrying_with` -> `retry_attempt` ->
`prove_masked_attempt` -> `reserve_and_build_pool_v1_pair_forest_mask_material_v1`
-> `StateOnlyMaskNonceStore::reserve` -> `reserve_fallible` -> `reservation_path`.

* V181, state_only_entropy.rs:961: exact capacity is the literal 69, independent
  of all input, witness, seeds, statement digest and nonce. The emission at
  ProverRwFullFuns.lean:14408 passes `69#usize`. The new natural-number bound
  is connected by a script-checked literal correspondence, not an elaborated
  theorem about the entire emitted reservation_path (its SHA cone is large).
* V178, state_only_entropy.rs:962: base is `self.directory`; argument is
  `reservation_name(SHA256(ATTEMPT_RESERVATION_DOMAIN || mask_nonce), empty,0)`.
  The recursion emits 32 pairs of hex digits then five bytes `.burn`.
  mask_nonce comes from the proof-account public key passed to
  `generate_for_mask_nonce`, not either private seed. The directory is created
  from `q["proof_dir"]` joined with `mask-nonce-ledger` at plan.rs:115.
  No private-seed content is an input to this path expression. This provenance
  does not prove allocation addresses, failure events or cache traces public.

## Additional direct application joins on the client route

All are in tools/r1-cost-probe/src/bin/devnet_spend/plan.rs, with base
`Path::new(q["proof_dir"].as_str().unwrap())`:

| Line | Argument | Source |
|---|---|---|
| 113 | `note-recovery.json` | literal; evaluated after recovery JSON construction |
| 115 | `mask-nonce-ledger` | literal; passed to durable store open |
| 119 | `proof.bin` | literal; evaluated after proof generation |
| 119 | `statement.bin` | literal; evaluated after proof generation |

These calls are not represented by op26's single reservation_path call in
ProverRwFull. Their initial allocator state can depend on preceding work.
The incoming request's proof_dir is not constrained by a Lean public-input
classification theorem in the inspected row model. Calling it public here
records its request provenance, not an added premise in a privacy theorem.

No direct String::with_capacity is present in devnet_spend, plan,
RealR1_client or the selected cost-probe prover. aspis-prover/pow.rs:26 has
`bytes.len()*2`, with its own callers passing 32-byte transcript state;
that module's PoW entry is not called by the inspected cost-probe prover
(which uses its own transcript). Other binaries/examples/tests are not the
selected devnet_spend root. Third-party/std indirect allocation call sites
(e.g. formatting/collect) are NOT certified exhaustively by this inventory.
That missing deployed binary reachability certificate is explicitly retained.

## Endpoint statement mismatch

ProverRwFullExternalFuns.op30 has type `Usize -> Result String`.
PV_CBL_AppendBundle.op30_source yields unconditional `ok empty`; its selected
callback has no allocator world input/output. op26 similarly returns PathBuf
without a world. PV_CBL_CallbackPublication.op26_source selects the old
JoinAdapter.reference, which builds a fresh byte vector; it does not select
the clone-first reference. The new proofs do not edit either dictionary.

The adapters added here transport complete results to an arbitrary consumer
that actually accepts them. They do not establish that the deployed endpoint
is such a consumer. A generic `congrArg` transport cannot supply that missing
instance, an allocator-state relation, or L1/L2/L3 noninterference.
