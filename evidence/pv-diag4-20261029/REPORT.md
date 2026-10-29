# PV_DIAG4 — D447 resumed diagnostic composition

Target not yet established. Branch `codex/pv-diag4-20261029`, candidate base `5a2df9074c`; exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`. No implementation, observer, simulator or trust-list edits; no wallet/key operations.

## Stage 1: fresh EJR V2 replay

The authority remains EJR blob `431494fb8678733178af8c5c58cb18fbcb49f3b9`, source SHA256 `4321909f01b6f4d578b5e4c2198ba59406418ef8bd85f6e177f34ae107ddb694`. Rejected historical cached source `0bb8dcc74e6d33492d386582c06836aca1ee35fc61ce898cc3afb8f6d1b20e16`, object `0cf5b991b623d35edd390a7898223015f07d28b01743aa659f06384a333ea66f`. No substitution.

Attempt 64500 failed because this job initially omitted a private `.olean.server` link; this was an input preparation error, corrected by pinning sidecars. Attempt 64501 freshly elaborates the exact EJR source with 730 recursively hash-checked dependencies and all 5,673 external objects checked. It exits 1 at line 100: **`No goals to be solved`** (`rfl` after `simp only`). Full output, exact source snapshot, dependencies, revision, wall/RSS/swap and axioms appear in the raw receipt. This is an authoritative-source/cohort replay finding, not a native witness-leak finding. The source is not edited.

`cohort-plan.json` lists the eleven affected modules in dependency order. Only `R1Z.PrivacyR1HeadlineV2` was attempted; no successful object was admitted. Its ten downstream consumers are blocked by that predecessor and were not compiled against the rejected cached variant. Thus no unchanged-consumer missing-declaration finding is claimed. The endpoint rebuild is incomplete for the exact recorded reason.

## Stage 2: sampler association

In progress; see `sampler-generation-chain.json` and the fresh receipts. The graph has no sampler entries. h7(2) recovers the original generation and the explicitly recorded historical numeral compatibility adaptation. No new edit of generated output and no STEP 4 regeneration is claimed.

## Remaining deliverable

Concrete diagnostic leaves, their honest joint law on the existing L1 coins, and complete client observer composition remain open. No endpoint premise removed. V370 remains the compiler/source preservation boundary; T stays exactly entropy_law, entropy_kernel, observation.
