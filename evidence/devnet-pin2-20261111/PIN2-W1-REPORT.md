# PIN2 W1 report: verifier-side source changes (A) binding, (B) checkpoint close

Branch `fix/pin2-verifier-20261110` from `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Commits (no trailer, not pushed):

- `43919c0a9f2` PIN2 (A): bind pool, deployment domain and withdrawal destination in r0 public_bytes
- `271869c946d` PIN2 (B): verifier checkpoint close instruction [7, seed_len, seed]

programs/aspis-pool and crates/aspis-prover are untouched. This report file is not committed.

## Changed files (sha256 before at 4bb3b3f, after at 271869c946d)

| File | Before | After |
|---|---|---|
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs | 4e209947ac75532af1c7d79f339050aab6b57379fc3962e1df9ff5602087787e | d326ede72fea8f7859fe3ed579cb62ee7ad1b91b22852348baf45229c6828791 |
| programs/r1-cost-probe/src/pool_route.rs | 43cfa25ec59e5349773599924d318a4b8fda923c4958760fcf1482d8fb2db9f0 | d238df64ba3c3bb80c126abc922616332de9ee74d924356969efb04154eba930 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs | 09ce3b480cf772c843315b9bcdabd9bf266f4065e5a524ae2a4d5560ea4feaf3 | 6a07bc7eea39efa067c1864b2e42747f1d222d8222c1e9b73f06aed0fd7d4a65 |
| programs/r1-cost-probe/src/r1_checkpoint_tests.rs (tests) | 7daeb3274f01b1f5ae87c040a694dc7759dbfa12fb02a5715461bc19cae45c26 | 0babdd8308e9960ad9322f962701153d2d70b897f726f91e0c9d9d50a2c6e653 |
| programs/r1-cost-probe/src/close_checkpoint_tests.rs (tests, new) | (new file) | a09f7fb7325499ec29cceb2c46e14946a41ad0238db5a2e064a2a60802246f7e |

r1_pool_adapter_original.rs (the differential-test copy of the old adapter) is unchanged.

## (A) Statement change

- `SemanticPublic` gains `destination: Option<[u8; 32]>`. `withdrawal_public` sets
  `Some(public.destination_token_account)`, `private_public` sets `None`. The field has
  `#[cfg_attr(not(feature = "r0"), allow(dead_code))]` because only the r0 serializer reads
  it; the r0 build (the verifier's) is unaffected by that attribute.
- `r0::Public::public_bytes` appends, after `frontier(&mut out, &after.next_frontier)?`:
  `pool[32]`, `deployment_domain[32]`, `has_destination` (1 iff Some), then `destination[32]`
  iff Some. The doc comment now says these are hashed through these bytes and that the source
  sequence number and source current root remain unserialized and unhashed.
- The terminal composition and every other function in the crate are unchanged.
- `pool` and `deployment_domain` are SemanticPublic's existing fields, i.e. the payment public
  input's `pool` / `deployment_domain` (as the brief specified). Whether these equal the
  statement's other copies (`live_snapshot.pool`, etc.) is checked elsewhere, not here.

### §9 byte layout (offset, length)

Transfer (variant tag 0), total 1520 bytes (was 1455):

| Offset | Len | Field |
|---:|---:|---|
| 0 | 1 | variant tag = 0 |
| 1 | 32 | anchor (8 x u32 LE) |
| 33 | 32 | nullifier |
| 65 | 4 | asset_id |
| 69 | 1 | has_recipient = 1 |
| 70 | 32 | recipient commitment |
| 102 | 32 | change commitment |
| 134 | 1 | has_amount = 0 |
| 135 | 8 | source next_pair_index (u64 LE) |
| 143 | 640 | source frontier (20 x 32) |
| 783 | 32 | next_root |
| 815 | 640 | next frontier |
| 1455 | 32 | pool (new) |
| 1487 | 32 | deployment_domain (new) |
| 1519 | 1 | has_destination = 0 (new) |

Withdrawal (variant tag 1), total 1524 bytes (was 1427):

| Offset | Len | Field |
|---:|---:|---|
| 0 | 1 | variant tag = 1 |
| 1 | 32 | anchor |
| 33 | 32 | nullifier |
| 65 | 4 | asset_id |
| 69 | 1 | has_recipient = 0 |
| 70 | 32 | change commitment |
| 102 | 1 | has_amount = 1 |
| 103 | 4 | amount |
| 107 | 8 | source next_pair_index |
| 115 | 640 | source frontier |
| 755 | 32 | next_root |
| 787 | 640 | next frontier |
| 1427 | 32 | pool (new) |
| 1459 | 32 | deployment_domain (new) |
| 1491 | 1 | has_destination = 1 (new) |
| 1492 | 32 | destination_token_account (new) |

### Callers

`grep public_bytes()` finds these callers, all of which hash or forward the function's output
and need no source change: crates/aspis-r1-cost-probe/src/{prover.rs (89, 113), dense.rs (102),
semantic.rs (49), r1_semantic.rs (70), host_semantic.rs (82), sim.rs, sim_owned31.rs,
sim_tests.rs}, examples semantic_gate.rs and r1p_sim_gate.rs, crates/aspis-statement/src/state_only_verify.rs
(1177, 1242), and Stream B's crates/aspis-prover (state_only_candidate_prefix.rs:815,
tests/r0_semantics.rs), which I did not touch. `cargo check -p aspis-r1-cost-probe --all-targets`
passes. No other source hard-codes 1455/1427.

### Tests (public_serializer_tests)

- `binding_tail_lengths_are_exact_for_both_variants`: 1520 / 1524, plus the tail bytes at the offsets above.
- `withdrawal_destination_changes_public_bytes`: three single-byte destination changes each change the output, keep its length, and leave bytes 0..1492 unchanged.
- `pool_and_deployment_domain_change_public_bytes_for_both_variants`: pool or domain bit flips at byte 0 and 31 change both variants and leave the frozen prefix unchanged.
- `frozen_layout_prefix_is_unchanged`: the first 1455 / 1427 bytes equal the verbatim frozen
  serializer (`old_layout_reference`) and have pinned SHA-256s,
  transfer `b47ffcf2df84a8e21f500de3e726cc25537d525629c1d034a3c8a5e744339db6`,
  withdrawal `8a4ccb41d781aea403c268ee029749ccc1bdd7aac193988a5d6c06d1986eeb7f`. I computed these
  by temporarily checking out the frozen file, running a throwaway print test against the real
  4bb3b3f `public_bytes`, and restoring the file. They are not derived from my reference copy.
- The existing differential test now checks against `loop_reference` (the frozen layout plus the
  tail, built from the public structs) and asserts the new lengths, replacing the hard-coded 1455/1427.

## (B) Checkpoint close

Tag **7**, not 6. Tag 6 is not on the release path (pool_route rejects it), but
`r1_pool_adapter::process` sends `Some(6)` to the legacy `lifecycle_finalize`, and
`r15_lifecycle_requires_recorded_signer_to_upload_or_seal` calls it directly. Reusing 6 would
overload that dispatch arm, so I took 7 as the brief allows. Before this change tag 7 fell
through to `stage2`, and pool_route rejected every tag-7 input.

Instruction data `[7, seed_len, seed...]`.

`pool_route::admitted` additionally admits exactly the inputs for which
`data.len() >= 3 && data[0] == 7 && data[1] as usize == data.len() - 2 && (1..=32).contains(&data[1])`
(`is_close_checkpoint`, constant `CLOSE_CHECKPOINT_TAG = 7`).

`close_checkpoint(program_id, accounts, data)` runs these checks in this order:
1. Data shape check repeated (`InvalidInstructionData`).
2. Exactly two accounts `[checkpoint, base]`, otherwise `NotEnoughAccountKeys`.
3. `checkpoint.owner == program_id`, `checkpoint.is_writable`, `!checkpoint.executable`, otherwise `InvalidAccountData`.
4. `base.is_signer`, otherwise `MissingRequiredSignature`.
5. Seed bytes must be valid UTF-8, otherwise `InvalidInstructionData`.
6. `Pubkey::create_with_seed(base.key, seed, program_id)? == *checkpoint.key`, otherwise `InvalidSeeds`.
7. Compute `base.lamports + checkpoint.lamports` with checked arithmetic (`ArithmeticOverflow`) before any write.
8. Zero every byte of the checkpoint data, set checkpoint lamports to 0, set base lamports to the sum. No other state is touched.

The doc comment says the instruction never writes a non-zero byte into a checkpoint. It is
dispatched from `process` as `Some(CLOSE_CHECKPOINT_TAG)`. I did not add a base-writable check,
because the brief lists none and the runtime rejects lamport credits to a read-only account.
The program_autofixer linter reported no issues on the handler.

Tests:
- pool_route: `close_checkpoint_admits_exactly_well_formed_seed_lengths` is exhaustive over
  every tag 0..=255, every declared length 0..=255 and actual seed lengths 0..=40. It also
  checks the 1/32/33/0-byte and mismatch edges and that `[6,1,x]` is rejected. Tag 7 is added
  to `lifecycle_and_legacy_prefixes_are_rejected`, whose tails are all malformed closes. The
  all-2-byte test is unchanged (`[7,0]` is rejected).
- close_checkpoint_tests.rs, through the crate entrypoint with the route guard:
  - success: data all zero, size and owner kept, lamports moved; 1-byte and 32-byte seeds work;
  - rejections, each checked to leave data and lamports unchanged: wrong signer key, non-signer
    base, wrong seed (three variants plus a seed derived for another program id), non-UTF-8 seed,
    wrong owner, executable or read-only checkpoint, 1 or 3 accounts, malformed data
    (`[7]`, `[7,0]`, short, extended, 33-byte seed, tag 6), the handler's own shape check, and
    lamport overflow.
- r1_checkpoint_tests.rs: `stage1_on_closed_then_recreated_checkpoint_matches_fresh` closes an
  occupied (0x55) seed-derived checkpoint, models re-creation (same size and owner, zero data,
  re-funded), and asserts stage1 gives the same result and the same account data and lamports as
  on a fresh fixture. It compares outcomes, so it holds whether or not the saved proof verifies.
  In the B-only run below it ran on the success path.

## Validation (local Mac only; no build host; no cargo-build-sbf; rustc 1.93.0, debug profile)

**macOS limitation.** The program crate's lib tests do not build on macOS at 4bb3b3f. LLVM
rejects `#[link_section = ".rodata.aspis_pool_program_id"]` because Mach-O needs the form
`segment,section` (baseline run: exit 101, 238 s, compile error). For every program test run
below I temporarily rewrote the four `link_section` attributes in r1_pool_adapter.rs and
r1_pool_adapter_original.rs as `cfg_attr(target_os = "solana", ...)` with a script
(scratchpad macstrip.sh), and reverted them before committing. The committed source keeps the
original attributes, and the before/after hashes above are of committed content.

| Command | Tree | Exit | Wall | Peak RSS | Result |
|---|---|---:|---:|---:|---|
| `cargo test -p aspis-statement --features r0 --lib public_serializer_tests` | 4bb3b3f | 0 | 28 s (cold) | 0.11 GB | 2/2 |
| `cargo test -p aspis-r1-cost-probe-program --lib --features pool-adapter,private-leaf-salts` | 4bb3b3f, no strip | 101 | 238 s | 0.73 GB | compile error (Mach-O link_section) |
| same | 4bb3b3f + strip | 0 | 5 s (warm) | 0.40 GB | 76/76 |
| `cargo test -p aspis-statement --features r0 --lib public_serializer_tests` | A | 0 | 3 s | - | 6/6 |
| `cargo test -p aspis-statement --features r0` | A | 101 | 283 s | 0.85 GB | 258/259; `pool_v1::format::tests::format_binding_pins_existing_primitives` fails (see below) |
| `cargo check -p aspis-statement` (no features) | A | 0 | - | - | no new warnings |
| `cargo check -p aspis-r1-cost-probe --all-targets` | A+B | 0 | 6 s | - | ok |
| program tests (as above) + strip | A+B | 101 | 4 s | 0.45 GB | 70/89; the 19 failures are listed below |
| program tests (as above) + strip, statement file temporarily at 4bb3b3f | B only | 0 | 3 s | - | 89/89 |

Swap stayed at 0 in every run.

**The format.rs failure.** It is in an untouched file and compares the literal constant
`POOL_V1_FORMAT_BINDING[8..21]`: the test expects `[..,1,1,1,1,1,1]` and the constant has
`[..,2,2,1,1]`. Nothing in this change can affect it. I did not rerun it at 4bb3b3f, so
"pre-existing" is an inference from that, not a measured baseline.

**The 19 A+B failures.** Every one of them stage1-verifies a saved proof under
docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/*/r1-s2-proof.bin:
nine checkpoint tests in each of the two adapter modules, plus the 1,200-mutation differential.
They now fail with `r1:error:Semantic` / `Parse`, because those proofs' Fiat-Shamir transcripts
were seeded with the old public_bytes. A proof made for the old layout no longer verifies, which
is what the binding is meant to do. With only change B applied, all 89 pass. So these tests stay
red until the six fixtures are re-proved under the new layout.

## Not done / follow-ups

- **Fixture regeneration (blocking for a green program suite).** The six saved
  format-adopt proofs must be re-proved under the new public_bytes, then the checkpoint and
  differential tests rerun. That is the measurement driver / prover job (Stream B/C). The fixture
  files are outside my file list and I did not regenerate them. The statement bytes (ASF8,
  1880 bytes) are unchanged; only the proof bytes change.
- No SBF build, no Lean mirror (W2), no devnet run.
- The program lib tests do not build natively on macOS (link_section). Either run them on Linux
  or gate the attribute with `cfg_attr(target_os = "solana", ...)`; I left that decision to the
  lead, since it changes verifier source.
- Clients must create checkpoints with `create_account_with_seed(base = payer)` for close to
  work. Checkpoints created any other way cannot be closed by this instruction.

target not yet established
