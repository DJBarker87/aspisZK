# Omitted callback edge (inventory finding)

Frozen revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, `programs/r1-cost-probe/src/lib.rs:50` (file SHA256 `e56fd18185d72d5b925da56fdd168a05c9bfea2da1c2d17058d097f74c66d4d8`):

```rust
verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)
```

The caller `programs/r1-cost-probe/src/lib.rs::first_decoded` invokes `verifier::tx1` then `Result::map_err(error)`. On its `Err(e)` branch the callback is `programs/r1-cost-probe/src/lib.rs::error(e)`; on `Ok(v)` it returns the SAME `v` without invoking the callback. The callback inventory occurrence is TX2:211, omitted by the canonical direct-call graph because it is passed as a function item. Add a callback-kind edge from first_decoded to error, conditional on tx1 returning Err, with the exact error argument and ProgramError return. Its transaction membership must be recomputed from the deployed union graph: the TX2 label is historical inventory data, not evidence of TX2 execution. This job does not edit the inventory, rename the callback, or claim native credit for it. Rule14 function-pointer quarantine remains applicable to dependent native proofs.

Inventory fields (proposed only): caller `programs/r1-cost-probe/src/lib.rs::first_decoded`; callee `programs/r1-cost-probe/src/lib.rs::error`; edge kind `Result::map_err callback`; source line50; condition `verifier::tx1 returns Err(e)`; argument `the SAME e`; result `the callback ProgramError`, with the Ok Vec retained unchanged. `verifier` resolves to `aspis_r1_cost_probe::verifier` by line2. The callback's own logging/runtime edge remains a separate obligation.
