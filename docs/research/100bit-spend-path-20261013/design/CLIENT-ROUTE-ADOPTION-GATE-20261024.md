# Client route adoption gate — 2026-10-24

Read-only lead assessment at research2c9f709196. This reconfirms the existing D162 integration obligation, not a new security target or newly discovered protocol flaw. Both deployed targets remain not yet established.

The selected privacy source path is RealR1_client::prove_for_proof_accounts, whose mutable proof_account(k) public nonce feeds StateOnlyAttemptSecrets::generate_for_mask_nonce on each entered outer attempt. Only two private32-byte seeds are sampled. Its source-to-model transport, complete native cleanup/retry/events and literal E1 association are still open in the unmerged prover candidate.

Current tools/r1-cost-probe/src/bin/devnet_spend/plan.rs:112 instead invokes prover::prove_masked_retrying with no proof-account callback. The generic wrapper uses StateOnlyAttemptSecrets::generate, the96-byte route excluded from the selected privacy target. The planner later places q[proof_account] in settlement and stage1 accounts (lines120/123), which does not tie that account to the sampler. Finding an exported selected adapter or passing its tests does not establish planner adoption. This assessment concerns these exact source files and call sites; it is not an inventory of every client or a deployment-binary claim.

Before client adoption, a worker must connect retained per-attempt proof-account public keys to the selected adapter and use precisely the successful attempt's key for publication/upload/settlement. Preserve mutable/adaptive policy, eight-attempt limit, fatal duplicate/durable errors, advanced ledger state and key retention for rejected/error attempts. Account keys must remain securely retained; no live key cleanup or chain operation is part of this audit. Do not silently keep a generic fallback or reinterpret the96-byte theorem as selected64.

This wiring change is already authorized by D162, but remains a gated candidate: concrete source/refinement and client-error tests, applicable source/artifact identity assessment and required performance checks must precede adoption. Existing protocol/verifier bytes, security metric, entropy primitive and E1 law remain unchanged. Current native-drop work does not itself close this client integration gate. Keep the final deployment identity audit tied to the actual entrypoint and client artifact.

Inspection commands were rg -n for prove_for_proof_accounts/prove_masked_retrying in crates,programs,tools,scripts, followed by direct reads of the identified adapter and planner. No tests, builds, key operations, or source edits ran. Source pins:

- tools/r1-cost-probe/src/bin/devnet_spend/plan.rs: `b267904b985adf2d432be68a77e5b5a697f69ae7a92ddad3ff84c60bfae84b62`
- crates/aspis-r1-cost-probe/src/RealR1_client.rs: `55ceff433f3370c5bb1bce69baabbfc7e1277e6e11d86de77eed066211e500f1`
- crates/aspis-r1-cost-probe/src/prover.rs: `76aafd05e9b9459253f810be324b80fa5404449f93d03edb5697cddc669d2c42`


Reviewed candidate: codex/cx-client64-20261024 at1dfbd5711684d73fc2ff664cfae9ae78f7dd34f8 supplies selected64planner/keymapping/inventorymigration with offlineRust/Pythonreceipts. D202recordsreviewandlimits. It remainsunmerged/unadoptedpendingfinalnativeprover/refinement/artifact/performancegates. The pinnedrootcalleraboveisunchanged;do notconfusecandidatebehaviorwithdeployedcoverage.
