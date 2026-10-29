# Deployed caller identifications — LOG D446

Work in progress on `codex/pv-rj4id-20261029`, base
`60a288b5461129634a3714d56756a1c64fdca7e4`. No deployed identification or endpoint
premise removal is credited by this checkpoint. Sources under crates/ and
programs/ are unchanged. Runjoin's branch/worktree remain read-only.

The native route is `devnet_spend::main` → `plan::run` → `plan::prove` →
`RealR1_client::prove_for_proof_accounts` → `prove_masked_retrying_with` →
`retry_attempt` → `prove_masked_attempt`. It does not instantiate the Lean
Runtime. Exact source pins, model statements and compliant focused receipts
will be recorded below.
