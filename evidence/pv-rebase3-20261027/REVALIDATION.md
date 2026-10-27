# Candidate proof re-validation inventory

All 661 candidate files matching `ProverRw*`/`PV_*` (642 active modules and 19 archived source copies) are enumerated with imports and client associations in `candidate-proof-inventory.json`. No existing Lean file is modified by this merge (all imported Lean differences are additions). No crates/ or programs/ file differs from the pre-merge candidate. Accordingly no changed extracted Rust body or modified existing Lean source triggers a focused recompilation here; no historical object is promoted to final closure evidence.

The changed native source dependency is `tools/r1-cost-probe/src/bin/devnet_spend/plan.rs`, plus its new `Client64_accounts.rs` module, new diagnostic `pv_client_gate.rs`, and the standalone lockfile path edge. There is no candidate extraction of the planner in these modules, so a native planner-to-extraction binding is a re-validation obligation rather than an existing kernel dependency.

Recheck the deployment association of these client-sensitive existing modules after the new binary is pinned:

- `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean`: RealR1_client, generate_for_mask_nonce, prove_for_proof_accounts
- `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullTypes.lean`: RealR1_client, prove_for_proof_accounts
- `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_FinalAuditP8.lean`: privacy_headline_deployed
- `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RW_Audit.lean`: privacy_headline_deployed
- `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RW_FrozenManifest.lean`: privacy_headline_deployed
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwEffectCallback.lean`: RealR1_client, prove_for_proof_accounts
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwEffectOwner.lean`: generate_for_mask_nonce
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwEffectRetry.lean`: RealR1_client, prove_for_proof_accounts
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwEffectSource.lean`: generate_for_mask_nonce
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwEffectTape.lean`: generate_for_mask_nonce
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwEntropyIteration.lean`: generate_for_mask_nonce
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwFullAudit.lean`: RealR1_client, prove_for_proof_accounts
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngExtractor005Local.lean`: RealR1_client, prove_for_proof_accounts
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngExtractor005Operations.lean`: RealR1_client, prove_for_proof_accounts
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngExtractor005Types.lean`: RealR1_client, prove_for_proof_accounts
- `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwStage3EntropyAudit.lean`: privacy_headline_deployed

All source/effect, RunJoin, E1/E2, L1/L2/L3 and final closure/axiom-audit premises remain. This lexical inventory does not certify a coherent final import-name resolution; shared env-J sources were not written. Newly imported research proof modules retain their historical status and need the lead’s final closure replay.

`import-revalidation.json` resolves shared names using the h' rebuild inventory and records the explicit candidate full-extraction cohort. Among 642 active modules, no resolved import closure reaches an added/modified Lean source. 495 closures contain unresolved repository/cohort imports, explicitly listed; these are not claimed green and require exact final cohort resolution before release replay. No shared source or object was overwritten.
