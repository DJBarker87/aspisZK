# NDZ automatic relaunch 1 — completion audit

Resumed from completed evidence commit c7386b13a6. The worktree was clean.
Read AGENTS.md, NDS handoff/procedure/runbook, NDZ handoff/procedure/runbook,
and the deployment recovery policy at its actual repository path:
`docs/research/100bit-spend-path-20261013/design/DEPLOYMENT-SOL-RECOVERY-POLICY-20261029.md`.

The prior task window spans approximately 10:13–12:53 on 2026-10-29,
about 2 hours 40 minutes against the approximately three-hour budget. This
relaunch does not reset that budget. Prior documented attempts include four
native-client compilation preflights (fourth successful), an initial validator
thread-limit failure, the default-feature buffer-failure probe and interrupted
deployment, then two full successful local spend runs. The final deployment/spend
replay replaced specifically missing CLI metadata; it reused the first run's
proofs. Transfer and withdrawal each used one proof-generation attempt; the
separate offline writer compatibility proof used one attempt. The final
buffer-failure recovery probe exited 1 intentionally. See NDZ_PROCEDURE.md and
individual resource receipts for the distinctions; these are not all independent
proof or release samples. No build, validator, proof, transaction or test-suite
attempt was launched in this recovery turn.

Recovery verification (read-only, local public receipts only):

- All 336 locally packaged raw receipts match their manifest sizes and SHA256.
  The other 6,956 manifest entries are the deliberately host-retained paced
  write/signature/transaction receipts described by NDZ_package.py; they were
  not downloaded or independently rehashed during this relaunch.
- NDZ_TRANSACTIONS.json and NDZ_METADATA.json.gz each contain the same 1,812
  unique signatures; every row matches its metadata slot, fee and error.
- Summed fees and CU equal NDZ_SUMMARY.json: 27,440,000 lamports and 13,504,306 CU.
- Initial payer minus ending payer equals locked rent + recoverable rent + fees
  exactly. Final buffer inventory is empty.
- No difference under crates/ or programs/ against frozen source 4bb3b3f51e.
- Existing test receipts report 12 policy and 31 lifecycle tests passing.
  No unchanged test suite or formal regression was repeated.

Stage 0's mention of Pool-before-registry describes the original driver inspected
at that gate. The final rehearsed configuration explicitly sets
`pool_initialize_after_registry=true`; its actual order is registry initialize,
schedule, activate, freeze, then fresh Pool initialization, as documented in the
procedure and runbook.

The assigned local-only work is complete. NDZ_HANDOFF.md and
NDZ_DEVNET_RUNBOOK.md remain the delivery. No public write, signature submission,
key access, key cleanup or push occurred during this relaunch. L188 obligation 5
remains open for the separate real-devnet execution and read-only association.
Stop at lead review; do not execute the public runbook in this worker.
