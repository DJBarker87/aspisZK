# Aspis: worst-case compute of the one-transaction verify-and-settle path

Status: in progress. Measurements and source readings only; nothing here is proved.
Labels: **[S]** read from source, **[M]** measured, **[A]** bounded by arithmetic.

Sources read: branch head 4045ecbdda3 as checked out in this worktree. The Pool source in
`programs/aspis-pool` shows no difference from the frozen Pool revision b936275465600469312d1f058cdc91ea2a11f3dc
(`git diff --stat` empty). The deployed Pool ELF is `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc`,
built with `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`
(research `evidence/pool-inventory2-20261109/NKZ_DEPLOYED_BUILD.json`; the feature string is truncated
in my reading after `pair-f`, so the third feature is inferred from the earlier build scripts). Without
`pair-forest-history-page-invariant-audit` and `pair-forest-direct-result-audit`, the strict page
decoder and the full result check run.

## Why the recorded pre-state cannot be edited into a rollover

[S] The proof binds the lane's live snapshot (leaf count, root, frontier): the verifier
reconstructs the statement from the lane account (`r1_pool_adapter_owned.rs` 302-325), and the
history page in use is fixed by the leaf count (`pair_forest.rs` 1230-1287: rollover only when
`n mod 256 = 255`). The recorded payments are on a young lane, so changing the page state alone
gives a rejected proof. The tool therefore builds a fresh, consistent state at any leaf count and
proves a fresh payment for it with the deterministic fixture witness (`prove_masked_fixture`, as
`pool_gate.rs` does), keeping every recorded account the fixture does not choose (program ids,
master with asset id set to the fixture's 77, registry, entry, payer, mint, vault, vault authority,
token program, the seventh account, slot, devnet rent).

## Cost drivers on the path

| # | Driver | Source | Controlled by | Range | Worst reachable by |
|---|---|---|---|---|---|
| 1 | Merkle parent digests: `nodes + distinct - 1` per tree, plus 66 leaf digests | `fused.rs` 772-806, `multiproof.rs` 343-383 | query set (transcript) | supplied nodes ≤ 296/296/254; C1/C2 always 22 distinct (queries drawn without replacement), folded 1..22 distinct; parents ≤ 909, digests ≤ 975 | prover only, by grinding masks; honest proofs sit near 800 nodes |
| 2 | Unused slot tail zero check, 8-byte words | `candidate.rs` 283-296 | same | falls as nodes rise | — (opposes 1) |
| 3 | Insertion sort of 22 keys, twice | `fused.rs` 756-770 | query order | 0..231 exchanges per call | prover only |
| 4 | Query sampler: always 8 squeeze pairs (16 digests, fixed); scan of 22..64 draws with a duplicate check | `transcript.rs` 40-59, `aspis-core/src/r0_transcript.rs` 193-226, 305-318 | transcript words | duplicates needed for draws > 22 | prover only; the digest count does not vary |
| 5 | Field arithmetic branches (conditional reductions) in parse, semantic, folds, stage D | throughout | proof and statement values | small | honest and prover |
| 6 | Root-page validation: strict decoder decodes `filled` roots canonically and scans the unused tail byte by byte | `history.rs` 119-175, `pair_forest.rs` 817-860 | lane leaf count `n` | filled 1..256 | honest (the Pool's own history) |
| 7 | Page path: genesis (zeroed page 0, scan 8,256 bytes, write two roots), same page (append), rollover (full current page, `create_program_address` for the next page, zero scan of 8,256 bytes, full page write, one more account) | `pair_forest.rs` 1225-1306, 1776-1817; `history.rs` 247-282 | `n` | three paths | honest: every 256th payment on a lane rolls over |
| 8 | Frontier checks, 32-byte compare per zero bit of the leaf count, three loops | `pair_forest.rs` 606-613, 1392-1398, 647-652 | `n` | 0..20 compares each | honest |
| 9 | Marker: absent (one System CPI), funded below rent (transfer + allocate + assign, three CPIs, two signed), funded at or above rent (two signed CPIs) | `processor.rs` 268-332, 450-485; `nullifier.rs` 189-266 | anyone can send lamports to the marker address beforehand | three states | **adversarial third party** (one lamport) |
| 10 | Withdrawal: SPL Token `transfer_checked` CPI and two token-account parses | `vault.rs` 387-582, `pair_forest.rs` 1783-1794 | operation | transfer or withdrawal | honest |
| 11 | Account count: `require_unique_accounts` is quadratic (12, 13, 17 or 18 accounts) | `processor.rs` 123-132 | operation, rollover | 12..18 | honest |
| 12 | Program-address derivations: all on the success path use a stored or hinted bump with one `create_program_address` (master, lane, checkpoint, pages, vault authority, vault token account in the Pool; master, checkpoint, lane, registry, registry programdata, entry, verifier programdata in the adapter). No bump search on the success path. The registry v1 path (`registry.rs` 186, 212) searches, but the recorded policy carries the immutable-deployment flag, which takes the v2 path. The bump-search fallbacks (`pair_forest.rs` 517-521, `registry.rs` 316-317, 364-372) run only when the stored bump fails to match, and those calls then reject. The marker uses `create_with_seed`: two SHA-256 calls, no bump | as listed | none on success | fixed | — |
| 13 | Heap: 256 KiB requested; heap cost is a function of the requested size only | runtime | submitter | fixed at 256 KiB (a smaller heap fails) | — |
| 14 | Proof buffer and account sizes: exact lengths are checked, so CPI data charges are fixed | `r1_pool_adapter_owned.rs` 509-521 | none | fixed | — |

A hostile submitter who did not make the proof can choose: the marker funding (row 9),
the payer, extra instructions in their own transaction (which cost them, not Aspis) and the
compute and heap requests. They cannot change the proof, the statement or the lane. Only the
prover can influence rows 1, 3 and 4, and only by re-randomising and grinding.

## Predictions (written 2026-11-11T19:17:36Z, before any measurement)

Baseline: X2, recorded withdrawal with the marker funded with one lamport, 1,341,563.

| Scenario (X2, withdrawal, one-lamport marker unless stated) | Predicted whole-transaction CU | Basis |
|---|---|---|
| Rollover (`n = 255`) | 1,354,000 (band 1,336,000 to 1,372,000) | Strict decode of 256 roots replaces a scan of about 8 KB of zero tail. The rollover adds a zero scan of the 8,256-byte next page, a page write, one address derivation and one account |
| Rollover (`n = 1023`) | rollover `n = 255` ± 2,000 | Same path; differs only in the frontier compare count and in proof noise |
| Same page, nearly full (`n = 254`) | 1,341,563 − 4,000 (band −12,000 to +5,000) | Decoding 255 roots replaces the tail scan |
| Genesis (`n = 0`, zeroed page) | 1,341,563 + 3,000 (band −8,000 to +12,000) | Zero scan of the whole page plus two root writes |
| Marker funded at full rent | one-lamport variant − 2,000 | One CPI fewer (matches the recorded difference, about 1,600) |
| Transfer, same scenarios | withdrawal − 6,000 to − 7,000 | No token CPI (recorded difference about 6,500) |
| Fixture proofs across seeds, same state | spread up to 6,000 | Node count and sort order variation (rows 1 to 5) |
| Run at a compute limit one unit below the measured cost | fails, no state change except the fee | Runtime semantics: exceeding the limit aborts the transaction and rolls back every account write |

## Measurements [M]

**Setup.** Tool `tools/r1-cost-probe/src/bin/one_tx_worst.rs` (sha256
`fee0631ccc572ee4bb73333302132abc4d65cbf49279e6db218a7f3b146e49f7`). It was built in the head tree `src`
(4045ecbdda3) with its own target directory (`target/native-wc-src`), using the host script
`evidence/future-version-20261111/host/fv_worst.sh`. It runs in LiteSVM 0.16.0 (agave 4.2.1) with
signature verification off, a 256 KiB heap and the real 1,400,000 CU limit. The deployed Pool ELF is
`e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc`, and the recorded transactions file
has sha256 `c510767e0d84930e223abcdb86cab72158bf23f3debd3eb550c061f2afa190fe`. The verifier ELFs are A6
`5dd5b2b16c00922813dec692ee348dda2a73a58cbfaabe5a2f591b0b8c5a003b`, X1
`7a77273b1dc64689a0eed1cc267c6e81c9f6d0ad2e17fe0be316243d3ae9a3d5` and X2
`dff6a4385d7ae6503e97a6672835aab3b0ad3937bfba0caa0a339e9508a2556c`. Each scenario proves a fresh fixture
payment with `prove_masked_fixture` and a seed byte, re-packs it with `to_summed_format`, verifies it on
the host and reads the 22 query positions from the verifier's trace. The tool checks the node count
against the nonzero blocks of each slot.

Checks on every run: on success, the lane image, the history page (and the next page on rollover), the
marker and the exact token movement all equal the values computed independently. All 417 successful runs
pass. Each full scenario is also run at a compute limit one unit below its measured cost. All 39 such runs
fail with `ProgramFailedToComplete` and leave every account unchanged apart from the payer's fee. A
transaction that exceeds its limit fails with no state change.

Receipts (host, 8 GiB cap, no swap): `WC-build-w1` (exit 0, 1:42 wall, 651,672 kB RSS);
`WC-run-w1` (exit 0, 0:05.5); `WC-run-w2` (exit 0, 10:11, 291,248 kB); `WC-run-w3` (exit 0).
Results: `evidence/future-version-20261111/worst-case/w1.json`
(`76eda6ae0e23f7bcffb4e05a515502f7c93aff5aed7d3231bad7358bddbff9a1`), `w2.json`
(`2be82394dca53c224b5fe276db8c5079a3d277db6e0c6401877bb3c89482ab1d`), `w3.json`
(`8451144af6c1b8de006cddbaf6a67e859fb26ac86f6f9b10a6b509eabec19b0e`) and `receipts.txt`.

**Pool state scenarios** (seed 1; whole transaction, marker funded with one lamport; the Pool's own
cost is the Pool's inclusive cost minus the nested verifier's):

| Scenario | Path, page fill before | A6 | X1 | X2 | Pool's own cost |
|---|---|---:|---:|---:|---:|
| Withdrawal, n = 255 | rollover, 256 | 1,350,628 | 1,342,968 | 1,366,487 | 140,305 |
| Withdrawal, n = 511 | rollover, 256 | 1,357,784 | 1,350,174 | 1,374,895 | 140,274 |
| Withdrawal, n = 1023 | rollover, 256 | 1,356,541 | 1,348,925 | 1,373,464 | 140,243 |
| Withdrawal, n = 254 | same page, 255 | 1,286,972 | 1,279,352 | 1,303,709 | 71,639 |
| Withdrawal, n = 3 | same page, 4 | 1,324,272 | 1,316,637 | 1,340,836 | 109,865 |
| Withdrawal, n = 0 | same page, 1 | 1,328,668 | 1,321,070 | 1,345,949 | 110,451 |
| Withdrawal, n = 0, zeroed page | genesis | 1,329,054 | 1,321,456 | 1,346,335 | 110,837 |
| Transfer, n = 255 | rollover | 1,343,060 | 1,335,396 | 1,359,085 | 130,854 |
| Transfer, n = 1023 | rollover | 1,347,058 | 1,339,420 | 1,363,789 | 130,792 |
| Transfer, n = 254 | same page, 255 | 1,277,855 | 1,270,224 | 1,294,514 | 62,238 |
| Transfer, n = 3 | same page, 4 | 1,319,054 | 1,311,452 | 1,336,252 | 100,464 |
| Transfer, n = 0, zeroed page | genesis | 1,316,038 | 1,308,391 | 1,332,511 | 101,436 |

The marker state changes only the Pool's cost, by the same amount in every scenario and build. Relative to
an absent marker, one lamport adds 4,097 and full rent adds 2,482.

Reading. The Pool's own cost depends strongly on the lane's position. The strict page decoder scans the
unused tail of the current page byte by byte (`history.rs` 165-167), which costs about 38,000 on a young
page and almost nothing on a full one. A rollover pays for decoding a full page, a zero scan of the
8,256-byte next page, a page write, one address derivation and one more account. The rollover is the
heaviest Pool path, about 30,000 above a young same-page payment. The recorded devnet payments were
young same-page payments. By source reading, n = 255 is the heaviest rollover position: among positions
with `n mod 256 = 255`, it has the most zero bits in `n` and `n + 1`, so it makes the most frontier
compares. The measurements agree, with 140,305 at n = 255 against 140,274 and 140,243.

**Proof variation** (withdrawal, n = 255, marker absent, seeds 2 to 101 in `w2.json`; 100 proofs. Seed 1, in `w1.json`, falls inside the same range):

| | A6 | X1 | X2 |
|---|---:|---:|---:|
| Nested verifier, lowest to highest | 1,207,037 to 1,221,004 | 1,199,338 to 1,213,441 | 1,222,335 to 1,238,830 |
| Fit: CU per Merkle parent digest | 164.5 | 166.2 | 194.4 |
| Fit: CU per insertion-sort exchange | 0.89 | 0.89 | 0.86 |
| Fit residuals | −205 to +228 | −201 to +228 | −200 to +229 |

Merkle parent digests ranged from 813 to 897 (the maximum is 909). Exchanges, summed over both sorts,
ranged from 128 to 308 (the maximum is 462). Seed 60 is the heaviest, with 834 supplied nodes, 897
parents and 224 exchanges. The heaviest measured case is that proof at rollover with the marker funded
with one lamport (`w3.json`):

| | A6 | X1 | X2 |
|---|---:|---:|---:|
| Heaviest measured: withdrawal, n = 255, seed 60, one-lamport marker | 1,361,665 | 1,354,102 | 1,379,491 |
| Same, marker absent (no third party involved) | 1,357,568 | 1,350,005 | 1,375,394 |

## Predictions against results

| Prediction (19:17:36Z) | Result | Verdict |
|---|---|---|
| Rollover n = 255, X2: 1,354,000 (band 1,336,000 to 1,372,000) | 1,366,487 | in the band, 12,487 above the point |
| n = 1023: n = 255 ± 2,000 | 1,373,464 (+6,977) | **miss**. The Pool's own cost differs by 62; the rest is proof variation |
| Same page n = 254: −4,000 (band −12,000 to +5,000) | −37,854 | **miss**, wrong size. The tail scan costs much more than I assumed |
| Genesis: +3,000 (band −8,000 to +12,000) | +4,772 | in the band |
| Full-rent marker: −2,000 relative to one lamport | −1,615 | point missed by 385 |
| Transfer: withdrawal − 6,000 to − 7,000 | −9,401 (Pool's own) | **miss**. I used whole-transaction figures that include proof noise |
| Seed spread up to 6,000 | 16,495 (X2 verifier) | **miss**, more than twice the figure |
| Below-limit run fails with no state change | 39 of 39 | held |

## Worst case

Measured part: the heaviest measured scenario above. Allowances [A] for what was not reached:

| Driver | Gap from the heaviest measured case | Rate | A6 | X1 | X2 |
|---|---|---|---:|---:|---:|
| Merkle parent digests (row 1) | 909 − 897 = 12 | fitted slope | 1,978 | 1,998 | 2,337 |
| Insertion-sort exchanges (row 3) | 462 − 224 = 238 | 15 CU each, my instruction-count estimate; the fit gives under 1 | 3,570 | 3,570 | 3,570 |
| Sampler draws beyond 22 (row 4), duplicates only | ≤ 42 draws, each scanning ≤ 22 accepted values | about 110 CU per draw, instruction-count estimate | 4,700 | 4,700 | 4,700 |
| Value-dependent branches (row 5) | observed fit residual range | — | 429 | 429 | 429 |
| **Allowance** | | | **10,677** | **10,697** | **11,036** |

| | A6 | X1 | X2 |
|---|---:|---:|---:|
| Heaviest measured [M] | 1,361,665 | 1,354,102 | 1,379,491 |
| + allowance [A] | 10,677 | 10,697 | 11,036 |
| **Worst case** | **1,372,342** | **1,364,799** | **1,390,527** |
| **Headroom under 1,400,000** | **27,658** | **35,201** | **9,473** |
| Headroom on the heaviest measured case alone | 38,335 | 45,898 | 20,509 |

No input reached in these measurements makes X2 exceed the limit. On X2, the honest rollover payment
with the heaviest of 101 fixture proofs uses 1,375,394. A third party who funds the marker with one
lamport adds 4,097.

Who can reach each part. The rollover is reached by honest use, once per 256 payments on each lane. A
proof with 897 parent digests is honest: it was the heaviest of 101 fixture proofs with different seeds. The marker funding is open to
any third party. The remaining allowance (12 more digests, the most adverse sort order, sampler
duplicates) is reachable, if at all, only by a prover who grinds mask randomness. The duplicate draws need
collisions among 18-bit draws, which a prover cannot grind for at a useful rate. That allowance is
nevertheless kept in the worst-case figure.

## Not measured, or bounded only weakly

- The sort and sampler allowances rest on instruction-count estimates from the source, not on the SBF
  disassembly. The fitted sort cost (under 1 CU per exchange) is far below my estimate, so this part is
  probably conservative. It is not measured.
- Statement values other than the fixture's (amounts, commitments, destination) were not varied. Their
  effect is covered only by the observed residual range of 429.
- The runtime is LiteSVM with its bundled SPL Token program. On the recorded withdrawal the replay
  reproduced the devnet Pool cost exactly, but a cluster feature change to syscall or CPI pricing would
  change every figure.
- The lane capacity limit, the frontier near capacity and page numbers above 3 were not measured. The
  source reading gives no extra cost for higher page numbers, and n = 255 is the heaviest rollover
  position by the frontier-compare count.
- The registry v1 path (bump searches) is not reachable with the recorded immutable-deployment policy
  and was not measured.

Target status: unchanged, not yet established. These are compute measurements, not a soundness result.
