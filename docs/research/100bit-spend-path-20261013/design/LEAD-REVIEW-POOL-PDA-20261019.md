# Lead review: Pool PDA study and constant-seed stored bumps (2026-10-19)

Reviewed: branch `codex/r1-pool-pda-20261019` (89396ac56, e1133a192);
study `design/POOL-PDA-STUDY-20261019.md`; evidence
`evidence/pool-pda-20261019/` (`part2-result.json`, `tail-result.json`,
`receipts/`). Mandate: `LEAD-DECISION-POOL-PDA-20261019.md` (option C).

## Part 2 (implemented): accepted

Stored canonical bumps for the constant-seed settlement PDAs (master, both
lane checks, V2 registry and entry, two programdata addresses) in
`programs/aspis-pool/src/{pair_forest,registry}.rs`; one
`create_program_address` with the stored bump each, ownership checks
unchanged; rejection paths keep their old error codes. Settlement CU falls by
4,123 on all six fixtures; stage 1 and nested stage 2 unchanged. Gates: SBF
build (Pool f2a30ebc…, 589,256 bytes, clean rebuild identical); Pool suites
(111/84/116/116 by feature set); mutations over every bump 0–255 on every
converted field, wrong key/lane/owner/signer, forged registry image;
rejection runs (wrong release, stale lane, replay); strict stack audit.

Recorded assumption (same as G_R1.8): a stored bump is trusted because the
Pool only ever signs with canonical bumps, so no Pool-owned image can exist
at a non-canonical address. A test records that the native check alone does
not exclude it.

Not converted: the withdrawal vault authority and vault token account (their
bumps are stored nowhere; storing them changes the master format the
verifier also reads). Legacy state/pair-state PDAs are off the R1 route.

The measurement used verifier ELF a70f30bd… (cu-bound pin); the verifier
source changed between bee5825f0 and bb134241e and was not rebuilt here.

## Part 1 (study): findings

- Inventory matches the cu-bound traces: constant seeds (master, lanes,
  registry side, vault pair) need authenticity only; per-transaction seeds are
  checkpoint, current page, next page on rollover, and the nullifier marker
  (searched twice). Only the marker needs uniqueness.
- Off-curve rate measured 0.5004 (10⁶ hashes) and 0.4999 (2·10⁶ marker
  candidates); attempt counts geometric within 0.8σ to 17 extra attempts.
- (A) tail rule on today's code: P(withdrawal > 1.3M) ≈ 4·10⁻¹⁰, P(> 1.4M) ≈
  3·10⁻²⁰; a marker-caused failure makes the note permanently unspendable,
  a checkpoint/page-caused one is recoverable.
- (B1) seed-derived marker: ≈360 CU fixed; needs a hashed nullifier (32-byte
  UTF-8 seed ≤ 224 bits); collision blocks a note, cannot double-spend;
  changes the marker address scheme. (B2) nullifier pages: griefable (page
  filling), rejected. (B3) the Pool runs the canonical search itself with
  sha256 + curve-validate syscall: same addresses, ≈385 CU per attempt instead
  of 1,500, worst ≈98k fixed; premise that the validate syscall uses the same
  on-curve test as `create_program_address` (checked in Agave 4.2.1 source;
  feature active on mainnet/devnet). (B4) existing checkpoint/page accounts
  authenticated by a stored or supplied bump; not for the marker.
- No live R1 accounts: no migration for any option; no verifier interface
  change.

## Decisions needed (user)

1. **Marker/page design:** worker recommends B3 + B4 (addresses, formats and
   the double-spend argument unchanged; deterministic bound ≈98k for the
   marker plus 1,500 per existing account; one new runtime premise). Fallback
   B1 (cheaper, changes the marker scheme and adds a hash premise to the
   freshness gate). Option A keeps a probabilistic rule.
2. **Vault bumps:** two reserved master-account bytes (changes the master
   format and so the verifier binary and its pins) or a Pool-only hint.
