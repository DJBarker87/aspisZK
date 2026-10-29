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

## Automatic relaunch 2 — stop boundary reconfirmed

Resumed from clean commit 6462a5c8a3. Read AGENTS.md, the preceding recovery
accounting, NDS handoff/procedure/runbook, NDZ handoff/procedure/runbook and the
SOL recovery policy. The original approximately 2h40 task window and all attempts
listed above remain charged to the same approximately three-hour budget; neither
automatic relaunch starts a new budget. No additional build, validator, proof,
transaction or test-suite attempt was launched in either recovery turn.

A local public-receipt integrity check again verified all 336 packaged manifest
entries; 6,956 host-retained entries were not fetched or independently rehashed.
All 1,812 unique signature rows match captured metadata slots, fees and errors;
fee and CU totals match the summary. Exact lamport conservation and empty final
buffers pass. The worktree has no crates/programs difference from 4bb3b3f51e.
This is a delivery-integrity check, not another runtime or release sample.

No RPC request, public write, signature submission, secret-key access, key
cleanup or push occurred in this recovery. Existing keys/ledgers remain retained;
this turn makes no new assertion about remote key presence or backup status.
The local-only assignment remains complete. Deliver NDZ_HANDOFF.md and
NDZ_DEVNET_RUNBOOK.md to the lead, then stop. Real-devnet execution and its
read-only association remain outstanding under L188 obligation 5.

## Automatic relaunch 3 — completed delivery retained

Resumed from clean commit 476545f9ce on the assigned worktree branch. Read
AGENTS.md, the existing recovery accounting, NDZ handoff/procedure/runbook,
NDS handoff/procedure/runbook and the recovery policy at its actual path above.
The original approximately 2h40 and all previously listed attempts remain
charged to the same approximately three-hour budget. No new build, validator,
proof, transaction or test-suite attempt was launched in this recovery turn.
The prior integrity audit remains the evidence; it was not repeated here.
The frozen-source comparison still shows no changes under crates/ or programs/.

No RPC request, signature submission, public write, secret-key access, key
cleanup or push occurred in this relaunch. No new remote key-presence or backup
claim is made. The assigned stages are complete and their committed delivery
remains NDZ_HANDOFF.md and NDZ_DEVNET_RUNBOOK.md. Stop at lead review; the
separate real-devnet run and read-only association remain open under L188
obligation 5. Automatic relaunch is not authorization to execute that runbook.

## Automatic relaunch 8 — delivery remains complete

Resumed from clean commit 4b38567e42 on the assigned branch. The incoming
message includes relaunch notices 4–8; the committed recovery record ends at
relaunch 3. No additional intervening execution attempts are evidenced here,
and no fresh budget is inferred. The original approximately 2h40 and all
attempts enumerated above remain charged to the approximately three-hour budget.

Read AGENTS.md, the NDS and NDZ handoffs/procedures/runbooks, the recovery
policy, summary and collection audit. No build, validator, proof, transaction,
RPC request or test-suite attempt was launched in this recovery. The existing
receipt-integrity audit was not repeated. A read-only Git comparison confirms
no crates/programs difference from frozen source 4bb3b3f51e.

The local rehearsal and requested runbook/handoff are complete. Existing
receipts report 1,812 finalized local workflow transactions, empty final buffers,
12 policy tests and 31 lifecycle tests passing. These are prior results, not
new samples. No public write, signature submission, secret-key access, key
cleanup or push occurred in this recovery; remote key presence and backup were
not rechecked. Stop at lead review. L188 obligation 5 still needs the separate
real-devnet execution and read-only association; this worker must not execute
the public runbook.
