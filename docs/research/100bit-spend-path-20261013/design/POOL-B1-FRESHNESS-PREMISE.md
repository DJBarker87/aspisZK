# Pool B1 marker: restated nullifier-freshness release premise (2026-10-19)

Mandate: `LEAD-DECISION-POOL-PDA-20261019.md`, "Follow-up decision" (B1 marker,
B4 page/checkpoint bumps, Pool-only vault hints). Design: `POOL-PDA-STUDY-20261019.md`
§B1, §B4, F1-F6. Implementation and evidence: branch `codex/r1-pool-b1-20261019`,
`../evidence/pool-b1-20261019/`.

Labels: **[implemented]** in the Pool source on this branch; **[premise]** a
named release premise, not proved here; **[for the lead]** a document update
this branch does not make.

## 1. Address function

[implemented] `programs/aspis-pool/src/nullifier.rs`,
`pool_v1_pair_forest_nullifier_marker_address(program_id, master, n)`:

```
n      = canonical 32-byte encoding of the nullifier (8 x u32 LE, each < 2^31-1;
         non-canonical encodings are rejected before hashing, as before)
d      = SHA-256("aspis-marker-seed-v1" || master || n)      (20 + 32 + 32 bytes)
seed   = pack7(d[0..28])                                       (32 bytes)
marker = SHA-256(master || seed || program_id)                 (= Pubkey::create_with_seed)
```

`pack7` reads the 224 bits of `d[0..28]` most-significant bit first and cuts
them into 32 consecutive 7-bit groups; group `i` is `seed[i]`. Every seed byte
is in `0x00..0x7f`, so the seed is ASCII (valid UTF-8) of exactly
`MAX_SEED_LEN` = 32 bytes, as the System program's `*_with_seed` instructions
require. `pack7` is injective on 224-bit strings, so `seed` determines
`d[0..28]` and conversely.

- Base (marker authority) = the forest **master** PDA,
  seeds `["aspis-pair-forest-master-v1", asset_mint]`, bump stored at master
  byte 7. The settlement already authenticates it by that stored bump (Part 2,
  one `create_program_address`), so the base costs no extra derivation, no
  extra account and no hint. The Pool signs as the master through
  `invoke_signed` with the stored bump. The master signs nothing else in the
  settlement; elsewhere it signs only its own creation at initialization.
- Owner = the Pool program id (the derivation's third input); the System
  program re-derives `create_with_seed(base, seed, owner)` and rejects a
  mismatch or an owner ending in `"ProgramDerivedAddress"`.
- Creation: `CreateAccountWithSeed` when the address holds no lamports;
  `Transfer` (only if below rent) + `AllocateWithSeed` + `AssignWithSeed` when
  it was prefunded by anyone. Both paths are tested natively and in LiteSVM.
- Replay detection reads the account at that address. Owner Pool + exact size +
  valid marker image is `NullifierAlreadyConsumed` (code `0x41532026`,
  unchanged); Pool-owned zero image is populated; System-owned empty is
  created; anything else is `InvalidNullifierMarkerAccount`; a different key is
  `InvalidNullifierMarkerAddress` (both unchanged).
- Scope: only the pair-forest R1 route (`ASQ8`, audit `ASF8`) uses this
  function. The legacy single-tree, pair-state and prepared-settlement routes
  keep `pool_v1_nullifier_marker_address` (the canonical PDA
  `["aspis-pool-nullifier-v1", pool, n]`); their pools are different accounts
  (state PDAs, not a forest master) and they are not R1 settlement routes.

Choice of base, for the lead: the study sketched a dedicated authority PDA
(`[tag, master]`). A dedicated PDA would need a new account in every
settlement and a Pool-only bump hint (it holds no data, and the master format
is frozen), costing one more `create_program_address` (1,500 CU) and 32
transaction bytes. The master already satisfies the mandate's conditions
(constant-seed Pool PDA, stored bump, authenticated as in Part 2). Switching to
a dedicated PDA later changes only the base argument and the account list.

## 2. Restated freshness premise

Old form (J1.R3 release gate "freshness", G_R1 account premises): a settlement
of nullifier `n` on pool `P` is accepted only if the canonical PDA
`find_program_address(["aspis-pool-nullifier-v1", P, n], Pool)` holds no valid
marker, and a successful settlement leaves a valid marker there; uniqueness
came from the canonical bump (the Pool signs only for the canonical bump).

Restated form for the pair-forest R1 route, **[premise] Freshness-B1**:

> Let `M(P, n) = create_with_seed(P, pack7(SHA-256("aspis-marker-seed-v1" || P
> || n)[0..28]), Pool)` for the forest master `P` authenticated by its stored
> bump. (a) A settlement whose request carries nullifier `n` and master `P` is
> accepted only if the account at `M(P, n)` is not a Pool-owned valid marker
> image, and every accepted settlement leaves exactly one valid marker image
> for `(P, n)` at `M(P, n)`. (b) No instruction of the Pool program deletes,
> closes, reassigns or rewrites a valid marker image on the R1 route.
> (c) Only the Pool can create a Pool-owned account at `M(P, n)`, because
> every System instruction that creates or assigns at a `create_with_seed`
> address needs the base `P` to sign, `P` is a Pool PDA, and the Pool signs as
> `P` only in the marker creation of (a) (and in the creation of `P` itself).

(a) is the Pool source on this branch (`plan_pair_forest_nullifier_marker_consumption_v1`,
`create_pair_forest_nullifier_marker_if_needed_v1`, the final copy in
`process_pair_forest_terminal_with_verifier_v1`); (b) is unchanged from the old
premise (the marker image is written once and never touched again; no close
route exists for markers); (c) replaces "the Pool signs only for canonical
bumps" with "the Pool signs as the master only for its own creation and for
`M(P, n)`", which is checked by inspection of every `invoke_signed` in
`programs/aspis-pool` (two sites use the master seeds:
`pair_forest.rs` initialization and the marker creation).

Consequence used by the release argument: if two accepted settlements carry
the same `(P, n)`, the second finds the valid marker written by the first at
the same `M(P, n)` and fails with `NullifierAlreadyConsumed`. This needs only
that `M` is a function (it is), not any hash property.

## 3. Named hash premise for the truncated SHA-256

**[premise] MarkerSeedCR-224**: no efficient adversary finds two distinct
canonical nullifiers `n != n'` for the same master `P` with
`SHA-256("aspis-marker-seed-v1" || P || n)[0..28] =
SHA-256("aspis-marker-seed-v1" || P || n')[0..28]`, and, for a given victim
`n` (public only after it is spent, or never), no efficient adversary finds a
note it can spend with a nullifier `n'` that collides with `n` in this sense
(second preimage). Generic costs: about 2^112 hash evaluations for a birthday
collision among the adversary's own nullifiers; about 2^224 for a second
preimage of a fixed seed.

Second address premise (already implicit in every Solana PDA argument, now
named for the `create_with_seed` derivation): **[premise] MarkerAddressCR**:
`SHA-256(P || seed || Pool)` does not collide with any other account address
the R1 route reads (Pool PDAs end their hash input in
`"ProgramDerivedAddress"`; a cross-format collision is a full SHA-256
collision).

What these premises are used for: only to rule out that an honest note's
marker address is already occupied by a different nullifier's marker, i.e.
**blocking** (an unspendable note). They are not used for double-spend
exclusion (section 4). The old PDA design needed no hash premise for
blocking beyond the PDA syscall; this is the one new premise B1 adds.

## 4. Why no collision can double spend

1. One nullifier, one address: `M(P, n)` is a deterministic function of the
   authenticated master and the nullifier in the proven request. There is no
   caller-chosen bump, seed or base: the Pool computes the seed itself and the
   base is the master key it authenticated, and the marker account key must
   equal `M(P, n)` (`InvalidNullifierMarkerAddress` otherwise).
2. One address, one account: a Solana address names one account, so there is
   no second record for the same `n` to consult or to fake.
3. A collision `M(P, n) = M(P, n')` with `n != n'` makes the spend of the
   second of the two notes fail (`NullifierAlreadyConsumed`, the marker image
   is never overwritten even if its recorded context differs). A collision can
   only make a marker look used; it can never make a used marker look fresh.
4. Forgery attempts on the address: an attacker can create Pool-owned zeroed
   accounts at `create_with_seed(B, s, Pool)` only for bases `B` it can sign
   for, never for the Pool PDA `P`; a pre-funded System-owned account at
   `M(P, n)` is accepted and taken over (Transfer/AllocateWithSeed/
   AssignWithSeed under the Pool's master signature); an account at `M(P, n)`
   assigned to another owner cannot be created without `P`'s signature, and if
   present is rejected (`InvalidNullifierMarkerAccount`, a block, not a double
   spend). Tested: `b1_b4_terminal_mutations_fail_closed_before_cpi`,
   `b1_plan_accepts_only_the_seed_address_under_the_master_base`.

Blocking caused by premise failure is per note and permanent for that note on
this program (as for any marker-caused failure in the old design), and is
excluded under MarkerSeedCR-224 except with negligible probability.

## 5. Other premises this change touches

- **F6 (stored bump / hint authenticates an existing account)** now also
  covers: the retained checkpoint (stored bump, byte 7, as the R1 verifier
  adapter already reads it), the current root page and, on rollover, the
  zeroed next page (2 hint bytes), the vault authority and the vault token
  account (2 Pool-only hint bytes). Each is one `create_program_address`;
  mismatches keep the old errors (`StateHistoryMismatch`,
  `InvalidRootPageAddress`, `InvalidVaultAuthority`, `InvalidVaultTokenAddress`).
  The premise is unchanged in kind: the Pool creates checkpoints, pages and the
  vault token account only at `find_program_address` bumps (checkpoint
  instruction, deposit/initialize routes), so no Pool- or Token-owned image
  exists at a non-canonical address. Natively, a non-canonical image with a
  matching bump is accepted; test
  `b4_noncanonical_checkpoint_and_page_with_matching_bump_are_premise_bound`
  records this boundary, as Part 2 did for lanes. A hinted non-canonical vault
  authority cannot pass because the authenticated vault token account records
  the canonical authority. The settlement creates no PDA account any more: the
  Pool still signs only with canonical bumps whenever it creates or assigns a
  PDA account.
- **J1.R16 syscall premises**: the accepted R1 settlement no longer calls
  `sol_try_find_program_address`; it calls `sol_create_program_address` (master,
  lanes, registry side, checkpoint, pages, vault pair) and `sol_sha256` (marker
  seed and address, plus the existing uses). Both are already J1.R16 premises.
- **Instruction data (client-visible)**: Pool `ASQ8` and audit `ASF8` data are
  now `body || [current_page, next_page, vault_authority, vault_token_account]`
  (4 bytes). Unused bytes must be 0 (`InvalidInstructionData` otherwise; bump 0
  is never canonical). The verifier still receives the re-encoded request (or
  the exact ASF8 statement without the suffix); no verifier, adapter or CPI
  interface change. Master, lane, checkpoint, page and marker account formats
  are unchanged; only the marker address changes.
- **Remaining `find_program_address` on the R1 route, rejection-only**: the
  Part 2 fallbacks in the two lane decoders and the V2 registry/entry checks
  run the canonical search only after the stored-bump check has failed, to keep
  the previous error codes; every such path ends in an error. No search runs on
  an accepted transfer, withdrawal or rollover.

## 6. Documents that mention the old marker PDA

[for the lead] Found with `git grep -i -E 'aspis-pool-nullifier-v1|nullifier[- ]marker
(PDA|address)|marker PDA|pool_v1_nullifier_marker_address|NULLIFIER_MARKER_SEED|markerAddress|canonical marker'`
over `*.md`, `*.txt`, `*.lean` (generated Aeneas files and evidence folders
excluded), plus a read of the J1 design notes. None is edited on this branch.
"Forest" = describes the pair-forest/R1 route and needs the B1 restatement;
"legacy" = describes a route that keeps the PDA marker (no change needed, but a
reader may want a pointer).

| Document | What it says | Route |
|---|---|---|
| `design/J1-ORACLE-CALL-INVENTORY-20261015.md` (lines ~123-151) | marker derivation "checks its canonical digest encoding and then" searches; `create_nullifier_marker_if_needed_v1`; 0/1/2-3 System CPIs with `create_account` | forest: now seed derivation (2 SHA-256, no search) and the `*_with_seed` CPIs via `create_pair_forest_nullifier_marker_if_needed_v1` |
| `design/J1-SELECTED-PATH-HASH-BOUNDS-20261015.md` (line ~40) | Pool ASQ8 PDA work counted from the inventory | forest: query counts change (marker: 2 `sol_sha256` instead of 2 searches; checkpoint/pages/vault: 1 `create_program_address` each) |
| `design/J1-RELATION-STATEMENT-20261015.md` (line ~71) | lists "freshness" as a separate release gate | forest: the gate is now Freshness-B1 + MarkerSeedCR-224 (sections 2-3) |
| `design/J1-R16-R19-RUNTIME-RELEASE-20261015.txt` | J1.R16 runtime premises (`sol_create_program_address`, SHA) | forest: add `create_with_seed` derivation semantics of the System program (`*_with_seed` instructions check `address == SHA-256(base‖seed‖owner)`, base must sign) |
| `design/POOL-PDA-STUDY-20261019.md` §1 rows 2, 5-8, 13-14; §B1; §5 | the old searches and the B1 proposal | forest: rows 2, 5-8, 13-14 now implemented as B1/B4 |
| `design/G_R1_9-POOL-SPLIT-CHECKPOINT-20261015.txt` (line ~31) | marker rollback/replay tests | forest: replay behaviour unchanged, address changed |
| `docs/research/v7-pool-nullifier-marker-atomic-lifecycle-20260830.md` (lines 6, 57) | "derive and plan the exact marker PDA from the Pool and canonical nullifier" inside the forest terminal | forest |
| `docs/research/v7-pool-eight-lane-concurrency-gate-20260827.md` (line 130) | "one master-Pool-scoped nullifier-marker PDA" | forest: still master-scoped, now `create_with_seed` |
| `docs/research/v7-pool-runtime-adversarial-audit-20260830.md` (lines 71-85) | audits `pool_v1_nullifier_marker_address` and the Pool-owned zero canonical marker | forest + legacy |
| `aeneas-verif/v7-pool-nullifier-marker-source-20260830/` (README line 25; `proof/V7PoolNullifierMarker{Source,Caller,Path}Bridge.lean`, `NULLIFIER_MARKER_SEED_TAG`) | Aeneas extraction of the canonical PDA marker derivation and its caller | forest: the extracted source is no longer the R1 marker path; a B1 extraction (seed packing, `create_with_seed`, classification) would replace it |
| `programs/aspis-pool/README.md` (lines 148, 262, 312, 387) | account lists "canonical nullifier-marker PDA"; seed table `[b"aspis-pool-nullifier-v1", pool, canonical_nullifier]` | both: the forest terminal list and the ASQ8 data layout need the B1 address and the 4 hint bytes |
| `crates/aspis-statement/src/pool_v1/README.md` (line 145) | PDA seed schedule of the marker | legacy (statement crate unchanged); forest pointer needed |
| `AspisFormal/AspisFormal/V5TheftStateTransitionReduction.lean`, `V5ProductionStateBridge.lean`, `V5FinalSecurityAccounting.lean`, `V5NullifierMarkerReplay.lean`, `Pool/NullifierMarkerV1.lean` | abstract `deriveMarkerAddress : Digest → Address`, `MarkerAddressCollisionEvent`, `expectedMarkerAddress`, `bumpIs255` | V5/legacy models; the abstract `deriveMarkerAddress` form fits B1 (instantiate with `M(P, ·)`; the collision event becomes MarkerSeedCR-224); `bumpIs255` is PDA-specific |
| `docs/reviews/mathematical-status-20260814.md` (line 205) | "two nullifiers map to the same marker PDA" as a failure mode | legacy wording; same failure mode under B1 (blocking only) |
| `docs/research/pool-v1-prepared-settlement-kernel-20260826.md` (line 194), `release/preflight/v5-production-freeze.md` (line 128), `SECURITY.md` | prepared-settlement / V5 marker PDA | legacy, unchanged routes |
| `results/v7-pair-forest-registry-v2-litesvm-20260830/README.md` (line 82) | "canonical marker rejects" replay row | forest: historical measurement, old address |
