# Lead review: Pool B1 marker, B4 bumps and vault hint (2026-10-19)

Reviewed: worker commit 48a8bd8a1 (branch `codex/r1-pool-b1-20261019`),
evidence `evidence/pool-b1-20261019/` (`b1-result.json`, `receipts/`),
premise note `design/POOL-B1-FRESHNESS-PREMISE.md`. Mandate:
`LEAD-DECISION-POOL-PDA-20261019.md`, follow-up decision.

## Accepted

- **Marker (B1).** seed = 7-bit packing of SHA-256("aspis-marker-seed-v1" ‖
  pool ‖ nullifier)[0..28]; address = `create_with_seed(master, seed, pool)`;
  one helper `pool_v1_pair_forest_nullifier_marker_address` used by the Pool,
  wallet and both drivers. Both old searches (plan, replan) removed; the
  "already consumed" error unchanged. Creation covers an empty and a
  prefunded address (1 lamport, full rent).
- **Lead ruling: the forest master is the marker authority** (`create_with_seed`
  base), instead of a separate `[tag, master]` PDA. It is already a
  constant-seed Pool PDA authenticated by its stored bump, saving an account,
  a hint byte and 1,500 CU. Invariant for the uniqueness argument: the master
  signs no other `*_with_seed` derivation. Any future use of the master as a
  with-seed base must use a disjoint seed domain and be reviewed against this
  note.
- **B4 and vault.** Checkpoint by its stored bump; current page, next page,
  vault authority and vault token account by four Pool-only hint bytes after
  ASQ8 (unused bytes must be 0), each checked with one
  `create_program_address`. The master format is unchanged; the verifier
  source and ELF (a70f30bd…) are untouched (only the `pool_gate` driver
  changed outside the Pool and wallet).

## Measured

Settlement CU, Part 2 → B1: transfer 13/255/1023 1,133,274 → 1,129,757,
1,170,548 → 1,161,066, 1,167,456 → 1,160,974; withdrawal 1,146,835 →
1,138,950, 1,184,373 → 1,170,523, 1,181,113 → 1,170,263. Stage 1 and nested
stage 2 unchanged.

Seed independence: over 35 seeded runs, Pool-only CU (settlement minus nested
stage 2) takes exactly one value per kind and history mode (transfer 94,990 /
126,348 / 94,863; withdrawal 104,440 / 135,848 / 104,313), including seeds
that cost 23 (marker), 15 (checkpoint) and 14 (page) attempts under the old
code, where the same seeds cost +1,500 CU per attempt. Traced runs show zero
`sol_try_find_program_address` calls.

Gates: SBF Pool 121f3e29… (605,704 bytes; clean rebuild identical); Pool
suites 118/87/123/123; mutations over every hint 0–255, wrong marker
authority/seed/owner, forged and foreign-owned markers, wrong master/payer
signer or owner; double spend rejected (0x41532026) for both kinds with and
without a prefunded marker; stack audit passes. Wallet 187 + 33 pass; one
note-context vector fails identically at the base (pre-existing, not this
change).

## Remaining

- `find_program_address` remains on R1 routes only on rejection fallbacks
  (Part 2's error-code compatibility), and off-route: legacy routes,
  deposit/initialise/checkpoint creation (must create at canonical bumps),
  the V1 registry branch and the off-chain hint helper.
- Documents naming the old marker PDA (premise note §6: J1 inventory,
  hash-bound and runtime notes, v7 marker lifecycle/audit, the Aeneas marker
  extraction, which no longer covers the R1 marker path) are to be updated;
  `MarkerSeedCR-224` is a named premise, not proved.
- The committed wallet `Cargo.lock` was stale at the base; a refreshed lock
  is owed.
- Changed files are not rustfmt-clean, deliberately (formatting can move
  panic line numbers and change the ELF).
- The second, tighter CU bound is next (pre-registered first).
