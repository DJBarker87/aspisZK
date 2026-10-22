# Prover commitment continuation 39

**Target not yet established.** D151 scope: deployed statement image (D146),
public statement/proof bytes and adversary oracle answers (D143); timing and
other side channels excluded. Trust items remain P1, P7, TrustedStd, E1, E2.
No new cryptographic or environment assumption is added.

Task base: `561dcef39ae048ca4baeaad40a3e2bf7fd704d10`.
Branch: `codex/cx-prover-commit39-20261022`. Work in progress.

## Stage 1: source ordering and exact ledger coupling

Read D143–D151 before changing the proof. The actual secure wrapper
`prove_masked_retrying` (prover.rs:327–334) obtains secrets using
`StateOnlyAttemptSecrets::generate`, with no witness argument. The generator
(state_only_entropy.rs:172–194) draws 96 bytes and selects only by nonzero
checks on the three blocks; no witness enters this selection. The public
context and binding (prover.rs:106–115) use public bytes, variant and nonce.
`prove_masked_with_attempt` reserves/builds at line 129 before its first
read of the compiled witness trace at line 132. Within the builder,
state_only_entropy.rs:392–447, reservation at 408 precedes entropy expansion.
The reservation path (901–916) hashes only the fixed reservation domain and
nonce and appends its hexadecimal encoding plus `.burn` to the wallet ledger
directory. Neither statement digest nor private seed nor compiled trace enters
the path. The statement digest is written only after successful create.

On an occupied path, native `AlreadyExists` returns `Ok(false)` (934), the
builder returns `ReusedMaskNonce`, `mask_error` maps that to `Error::Semantic`
(prover.rs:172–177), and the retry owner aborts (371–374). It does not consume
another proof attempt or publish proof bytes. Byte-blind create/write/fsync
faults remain environment behaviour rather than a probability charge.

This source argument concerns the concrete OS-generated wrapper. The generic
`prove_masked_retrying_with` callback and `generate_for_mask_nonce` do not
establish a uniform independent nonce for an arbitrary caller; no universal
claim about such caller-supplied nonces is made.

`ProverCommitLedgerCoupling39` proves full state equality for the shared
reservation transition and preparation prefix; collision after injected
additions implies duplicate; duplicate preparation prevents either real or
ideal continuation from running. Both error and retained environment state
coincide. The theorems quantify arbitrary finite ledgers and schedules,
with no ledger cap and no collision probability term. They are model-prefix
laws, supported by the source-order inspection above, not a complete
source-to-FSExperiments conversion or a successful-continuation join.

J9160–J9161 were rejected elaboration drafts (ambiguous opened names, then a
qualified secret alias). J9162 compiles the four final prefix theorems:
exit 0, wall 1.85 s, peak RSS 4,151,728 KiB, zero swaps; axioms only
[propext, Classical.choice, Quot.sound]. The exact source overlay, dependency
fingerprint and raw receipts are retained in the part 39 evidence directory.
Only this job's new module was installed; earlier drafts of it were snapshotted
before replacement. No inherited shared module/object was overwritten.
