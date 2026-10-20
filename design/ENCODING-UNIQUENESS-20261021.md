# Frozen R1 / Pool encoding uniqueness — 2026-10-21

Verdict: no non-canonical field-encoding alias found in the frozen R1 / Pool parsers. Field limbs reject ≥ p; raw addresses and integer seeds retain their full values.

Scope: branch `codex/cx-encoding-inj-20261021`, base `3657df3e0`.
No shipped implementation changes. The question is injectivity of accepted
wire encodings into the complete logical statement, including raw account
addresses and transcript bindings, not of the semantic field projection alone.

Frozen ELF identities (SHA-256, not git commits):

- default verifier: `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`
- devnet verifier: `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78`
- Pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Source-to-pin evidence is the existing
`docs/research/100bit-spend-path-20261013/evidence/asq8-kani-20261021/relocation-elf-identities.json`
and corresponding relocation build receipts. This job adds native tests and
source hashes, not another SBF rebuild.

## Inventory

Here `p = 0x7fffffff`. “Yes” means injective on accepted encodings of
that field into its **typed logical value**. A 32-byte Solana address is a
byte array, not eight M31 values. An integer ≥ p is not non-canonical unless
the format actually declares it a field limb. Every range is half-open.

Decoder paths below are repository-relative; function names identify the
actual source, including the feature-selected fast readers. E1–E7 name the
native tests in `tools/encoding-uniqueness/src/lib.rs` in source order;
P6 names existing exhaustive solver evidence described below. S denotes
source inspection, not a newly executed test of the whole route.

### Public payment and statement fields

| Field (all limbs where applicable) | Decoder / source | Word ≥ p | Injective | Evidence |
|---|---|---|---|---|
| Private transfer recipient **owner**, change owner, secret key, salts, spent-note values, membership-path siblings and pair witness | No public byte decoder: prover witness only; `pair_forest_copy_builder::records` is off chain | May retain raw owner words in prover; not an accepted on-chain public field | N/A to wire parser | D96; `BuilderRuntimeJoin`; see formal interpretation |
| Deposit owner key and salt (AS8D and legacy deposit) | `programs/aspis-pool/src/deposit_transport.rs::decode_deposit_instruction_with_magic_v1`, via `decode_digest_canonical`; AS8D wrapper in `pair_forest.rs` | Rejects every non-canonical limb | Yes | S; E1 scalar/digest decoder |
| Deposit amount | Same decoder, `u32::from_le_bytes`, then `0 < amount < VALUE_LIMIT = 2^30` | Rejects | Yes; safe exact lift to M31 | S |
| Initialization and master identity asset ID | `instruction.rs::decode_initialize_instruction_v1`; `pair_forest.rs::decode_pair_forest_initialize_instruction_v1`; `pool_v1/format.rs::decode_pool_identity_v1` | Rejects explicit `asset_id >= P` | Yes | E7 identity; S initialization |
| Payment asset ID | `pool_v1/payment_relation.rs::decode_common` | Rejects explicit `asset >= P` | Yes | E2, E3, P6 |
| Anchor root / historical root | `payment_relation.rs::decode_common` → `atomic_statement.rs::decode_digest_canonical` | Rejects | Yes | E2, E3, P6 |
| Public nullifier (not its secret preimage) | Same `decode_common` → `decode_digest_canonical` | Rejects | Yes | E2, E3, E5, P6 |
| Transfer recipient commitment | `payment_relation.rs::decode_pool_v1_private_transfer_public_v1` → `decode_digest_canonical` | Rejects | Yes | E2, E3, P6 |
| Transfer / withdrawal change commitment | Transfer decoder above / `decode_pool_v1_withdrawal_public_v1` → `decode_digest_canonical` | Rejects | Yes | E2, E3, P6 |
| Withdrawal amount | `decode_pool_v1_withdrawal_public_v1`: raw u32, then `validate_pool_v1_withdrawal_public_v1` | Rejects `0` and `>= 2^30`, hence every `>= p` | Yes; exact field lift | E3, P6 |
| Transfer fee/reserved amount word | `decode_pool_v1_private_transfer_public_v1` | Only exact `POOL_V1_CANONICAL_FEE` bytes accepted | Yes | E3, P6 |
| Withdrawal destination token account | `decode_pool_v1_withdrawal_public_v1`: exact 32-byte copy, nonzero check | Keeps raw bytes; **no reduction** | Yes as an address; absent from semantic projection | E4, P6; Pool uses exact address |
| Pool address and deployment domain | `payment_relation.rs::decode_common`: exact 32-byte copies | Keeps raw bytes | Yes as byte arrays | P6; E6 checks raw-byte binding |
| Anchor sequence | Same `decode_common`: u64 LE, `validate_common` capacity bound | Keeps integer, but rejects beyond leaf capacity (including ≥ p) | Yes | S, P6 |
| ASF8 master, checkpoint and selected lane addresses | `pair_forest_terminal.rs::decode_terminal_common_boxed_v1` | Keeps raw bytes | Yes as addresses | S, E6 public hash mutation |
| ASF8 checkpoint sequence | Same decoder: u64 LE | Keeps full integer | Yes; not reduced to M31 | S; E7 analogous retained checkpoint field |
| ASF8 historical global anchor | Same decoder → `decode_digest_canonical` | Rejects | Yes | E2 |
| ASQ8 verifier profile, release, Pool program; registry/policy bindings; identity mint/token program/domain | `decode_pool_v1_pair_forest_terminal_request_v1`; `format.rs::{decode_pool_identity_v1,decode_verifier_policy_v1}`; `verifier_registry.rs` V1/V2 decoders | Keeps raw bytes, validates binding rules; not M31 | Yes as typed bindings | P6 request; S registry/identity |
| Live snapshot current root and frontier[0..20) | `pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1` → `decode_digest_canonical` | Rejects | Yes | E2 |
| Live snapshot sequence and next pair index | Same decoder: u64 LE, capacity/coherence validation | Keeps integer; rejects out-of-capacity values | Yes | S |
| Live snapshot pool/domain and fixed format bindings | Same decoder: raw copies / exact fixed constants | Keeps raw bytes / exact constant | Yes | S |
| Candidate afterstate next root and next frontier[0..20) | `pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1` → `decode_digest_canonical` | Rejects | Yes | E2; adapter also re-encodes and compares candidate bytes |
| Candidate next pair index | Same decoder: u64 LE, capacity validation | Keeps integer; rejects out-of-capacity values | Yes | S |
| ASR8 returned nullifier, next root and next frontier | `pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_result_v1` → canonical digest and afterstate decoders | Rejects | Yes | S; shared primitives E1/E2 |

### Persisted Pool accounts and R1 continuation checkpoint

| Field | Decoder / source | Word ≥ p | Injective | Evidence |
|---|---|---|---|---|
| Pool master next checkpoint sequence; last checkpoint lane sequences | `pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1` | Raw u64; lane sequences capacity-bounded | Yes as integers | S |
| Pool checkpoint global root | `pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1` → `decode_digest_canonical` | Rejects | Yes | E7 |
| Pool checkpoint sequence | Same decoder: u64 LE | Keeps raw full u64 | Yes; all eight bytes enter checkpoint PDA seed | E7 includes p, p+1, 2^31 and u64::MAX |
| Pool checkpoint lane sequences[0..8) | Same decoder: u64 LE, `<= POOL_V1_PAIR_CAPACITY` | Rejects out-of-capacity integers | Yes | S |
| Pool lane tree root/frontier | Frozen Pool `pair_forest.rs::decode_lane_account_from_program_invariant_v1`; verifier `r1_pool_adapter.rs::decode_lane_from_pool_release` | **Both reject** via `decode_digest_canonical`, even active frontier nodes | Yes | S; E1; E2 shared digest fields |
| Pool lane next leaf/pair index | Same readers: u64 LE and capacity check | Rejects out-of-capacity integers | Yes | S |
| Pool retained history roots | `history.rs::read_retained_root`; full reader `validate_root_page_bytes`; statement `root_history.rs::read_root_history_page_root_v1` | Rejects each root actually decoded | Yes per decoded root | S; invariant header-only path is not a decoder for unread slots |
| Nullifier marker stored nullifier / retained anchor root | `pool_v1/nullifier_marker.rs::decode_pool_v1_nullifier_marker` | Rejects | Yes | S; E5 address boundary |
| R1 checkpoint gamma, kappa, alpha[0..2), claim, accumulator rhs (WideExact, eight M31 limbs each) | `verifier.rs::resume` → `Reader::e` → `field/wide_exact.rs::WideExact::from_le_bytes` → `from_limbs` | Rejects any limb ≥ p | Yes | E1, E6; checksum repaired for every mutation |
| R1 checkpoint rho, semantic_alpha[0..10), z[0..2).x/y, accumulator power and weights[0..64) (QM31, four M31 limbs each) | `resume` → `Reader::k`; `read_checkpoint_semantic_alpha`; `read_checkpoint_weights` → `QM31::from_le_bytes` → `CM31::from_le_bytes` → `M31::from_le_bytes` | Rejects any limb ≥ p | Yes | E1, E6 |
| R1 checkpoint query indices[0..22) | `resume`: raw u32 then `validate_checkpoint_queries` | Rejects ≥ 2^18 and duplicate indices | Yes | S |
| R1 checkpoint proof hash, full-public hash, transcript state, C1/C2 Merkle roots, checksum | `resume` / `Reader::raw` | Keeps raw 32-byte digests; these are SHA-256 bytes, **not Poseidon M31 digests** | Yes as byte arrays | E6; S |
| R1 checkpoint variant, next query, status and reserved header | `resume` byte checks | Only admitted tag/status/range and zero reserved bytes | Yes for decoded state | S |

The ordinary M31 primitive is `crates/aspis-core/src/field.rs:239`:
`v = u32::from_le_bytes(bytes); if v >= P { None } else { Some(M31(v)) }`.
It neither masks bit 31 nor reduces p to zero. CM31 and QM31 call that
primitive on every component. WideExact independently checks all eight limbs.
No public field-byte decoder in this inventory reduces modulo p.

### Other entrypoints retained in the frozen Pool

The frozen Pool still dispatches legacy initialization/deposit/private-spend,
prepared-settlement and pair routes; they are not an alternate R1 engine.
Their field families follow the same policy:

| Field family | Decoder | Behavior / injectivity | Evidence |
|---|---|---|---|
| Legacy/pair spend anchor root, nullifier, recipient/change commitments, asset ID, withdrawal amount/destination | `programs/aspis-pool/src/instruction.rs::{decode_statement_common,decode_private_transfer_with_magic_v1,decode_withdrawal_with_magic_v1}` | Digests/asset reject ≥ p; amount range rejects; destination raw exact. Yes per typed field | S |
| Historical envelope anchor root/nullifier | `pool_v1/historical_anchor.rs::decode_historical_anchor_envelope_v1` | Canonical digest rejection. Yes | S |
| Legacy/pair pool state root/frontier and identity asset | `state.rs::PoolStateV1::decode`; `pair_state.rs::{decode,decode_from_program_invariant}` and shared tree/identity codecs | Canonical digest/asset rejection; integer counters exact. Yes | S |
| Prepared settlement source root/frontier, candidate roots/frontiers, append receipt roots, payment root/nullifier/output fields | `prepared_settlement_format.rs::{digest32,decode_receipt,decode_prepared_settlement_plan_v1}` and payment/afterstate codecs | Canonical digest rejection. Yes | S |
| Prepare/settle/cancel selection bindings, account identities, time slots, sequence/page/slot counters | Corresponding `*_instruction.rs` decoders; `prepared_settlement_format.rs` | Raw fixed bytes and LE integers, no field reduction. Yes per typed field | S |

Proof-carried field openings and sumcheck/FRI messages also reject ≥ p:
`candidate.rs::parse_shape`, `compact.rs` canonical QM31 storage checks,
`r1_wire.rs::Prefix::parse` / `parse_record`, `r1_semantic.rs` opening
readers, and the final-message canonical scan. Their M31/QM31/WideExact
words are trace/message values, not additional public recipient-owner
inputs. Salt, Merkle-path and SHA roots remain raw bytes. Transcript hash
**sampling** (`sampler.rs`, reduction into the challenge field) is deliberately
many-to-one; it is not an accepted wire field decoder or an account seed.

## Native evidence

Focused harness: `tools/encoding-uniqueness/`. No keys or live accounts are used.

Final frozen-source run: **7/7 passed**, exit 0, 20.627 s wall,
500,088 KiB peak process RSS, 521,510,912 bytes cgroup peak, **0 swaps**.
Scope: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Cargo release profile, `-j 4`, locked/offline dependencies.
Exact command, environment, revision and measurements:
`tools/encoding-uniqueness/evidence/receipts/frozen-native/receipt.json`;
stdout records all seven successful test names. `#print axioms`: N/A,
no new Lean theorem or compilation.

The native command links the frozen decoder/verifier implementations and
uses the existing `format-adopt-20261019/fixtures/transfer-1023/` public/proof
fixture also used by the D78-era checkpoint harness. A real hash, unchanged
saved proof, strict tx1 at split 10, tx2 and resume all succeed. This is not
a new simulated-proof or P_R1 generation run, nor an SBF execution test.

Coverage:

- E1: M31 boundaries 0, 1, p−1, p, p+1, 2^31 and u32::MAX;
  every digest/WideExact limb and every QM31 component.
- E2: **1,508** invalid ASF8 mutation attempts (1,131 distinct inputs): each field word independently
  replaced with p, p+1, 2^31 and u32::MAX. The accepted baseline re-encodes
  exactly. Covers historical anchor, both roots/frontiers and all transfer
  payment field words.
- E3: **232** invalid ASQ8 field mutation attempts (174 distinct inputs) across both payment variants,
  plus eight invalid amount/fee mutations; accepted baselines round-trip.
- E4: withdrawal destination words 0, p, 2^31, u32::MAX remain distinct
  raw addresses (other address bytes nonzero), round-trip exactly, and give
  distinct full ASF8 hashes. No reduction identifies those statements.
  These are parser-level accepted records, not four newly generated proofs.
- E5: canonical zero nullifier permits marker derivation; **32**
  non-canonical mutation attempts (24 distinct inputs) are rejected by the actual exported marker-address
  function before it hashes or calls `create_with_seed`.
- E6: **1,472** checkpoint field-word mutation attempts (1,104 distinct inputs), with checksum repaired
  each time, all fail `resume` with `Error::Checkpoint`. This prevents the
  checksum check from masking a lax scalar decoder. A raw-public-address
  mutation also fails checkpoint/public binding.
- E7: Pool checkpoint root has **32** rejected limb mutation attempts (24 distinct inputs); full u64
  checkpoint sequences p, p+1, 2^31 and u64::MAX round-trip exactly;
  identity asset rejects all four non-canonical words.

The mutation array deliberately lists both p+1 and 2^31, which are equal;
attempt counts above include that repeated boundary. The complete ≥ p range is justified by the decoder's unsigned comparison,
not by pretending these boundary samples enumerate 2^32 words. ASQ8's
existing P6 proof additionally covers all 320-byte inputs.

`frozen-source-comparison.json` compares 259 relevant inputs with the earlier
identity-checked ASQ8 packet. Four inherited research differences exist at
the task base: prover salt-loop refactor; off-chain trace-validation refactor;
and EOF-only Kani/extraction additions in copy-builder/Poseidon files.
All actual decoder files are already equal. The final run overlays those
four files **only in the private host copy**, making all 259 inputs exact
matches to the frozen packet. `frozen-run-inputs.json` pins their hashes,
the seven-test source and the generated standalone Cargo.lock.
Reference revision: `02a646121c59587352913bc19708bde25bba33fb`;
task harness revision: `31fbbbbc75b8594b97a8ca135f95ccac79070156`.
`run-frozen-host.py` is the recorded overlay/validation/launch script.

The preliminary task-base six-test run passed (53.796 s, 553,796 KiB,
0 swaps); retained separately under `receipts/native/`. The final replay
has changed frozen source inputs and an additional test, not an unchanged
regression rerun. One preparation attempt stopped before any build because
the source upload omitted pinned README files; the script now copies those
read-only inputs too. No compiler/test failed, no memory kill or cap increase.
No large build or formal manifest was launched locally.

## Formal interpretation and proposed changes

### Seeds and recipients

1. **Nullifier marker:** `programs/aspis-pool/src/nullifier.rs::pool_v1_pair_forest_nullifier_marker_address`
   first calls `decode_digest_canonical`. Only then does it compute
   `SHA256("aspis-marker-seed-v1" || master || canonical_nullifier_bytes)`,
   pack the first 224 bits into a 32-byte ASCII seed, and call
   `Pubkey::create_with_seed(master, seed, program_id)`. The Pool terminal
   obtains the nullifier encoding with `encode_digest_canonical` from its
   already decoded request. There is no p/zero or high-bit alias available
   to produce a second marker for the same field nullifier. The lower-level
   `pool_v1_pair_forest_marker_seed_v1` does not validate its argument by
   itself; the exported address function does. Hash truncation can cause
   different nullifiers to share a seed; that is the opposite direction
   from this encoding-alias question and is not information-theoretic
   injectivity of the cryptographic address function.
2. **Vault:** `vault.rs::{pool_v1_vault_authority_address,pool_v1_vault_token_account_address}`
   use fixed domain strings plus the full raw Pool public key. The forest
   master uses fixed domain plus raw mint key, and lane uses master plus
   lane ID. Neither nullifier limbs nor recipient-owner limbs enter vault
   derivation. Raw Pool/mint bytes are exact identities, not reduced fields.
3. **Checkpoint/history:** `pair_forest.rs::pool_v1_pair_forest_checkpoint_address`
   uses all eight LE bytes of `checkpoint_sequence` plus master. History
   addresses use full raw lane/Pool keys and exact page-number integers.
   Sequences p and 0 are different integers and different logical snapshot
   identifiers, even if someone separately casts both into a field.
4. **Recipient:** transfers expose a canonical **commitment**, not an
   on-chain recipient-owner account seed. Withdrawals expose the exact
   raw `destination_token_account`; `pair_forest.rs::process_pair_forest_terminal_v1`
   validates and transfers to that exact `Pubkey`. The address is absent
   from the algebraic semantic projection but remains part of the full
   payment/ASF8 statement. Stage 1 hashes original public bytes; checkpoint
   resume compares `hash(public_bytes)`. Stage 2 reconstructs and encodes
   the authenticated full statement before that comparison. Distinct raw
   destinations are distinct full statements and cannot reuse the same
   checkpoint without a hash collision (or breaking the separately required
   checkpoint provenance). This is a cryptographic binding claim, not a
   proof that SHA-256 is mathematically injective.
5. **Bump hints:** Pool strips four suffix bytes before ASQ8 CPI. The
   selected frozen path checks page/vault hints against actual derived
   accounts and requires unused hints to be zero (`pair_forest.rs`,
   `plan_pair_forest_spend_layout_v1`, `process_pair_forest_terminal_v1`).
   P6's suffix-strip theorem alone does not authenticate hints. They are
   not M31 limbs, and cannot bypass the nullifier canonicality check.

### What the Lean statements mean

The algebraic soundness relation is over **field elements**, not unrestricted
u32 storage words. `docs/research/100bit-spend-path-20261013/lean/SpendRelation.lean`
defines `Witness K`, `Rspend`, and concrete `Wspend = Witness M31Exact`;
owner/key/salt/path/commitment coordinates have field type, and values are
bounded integers `Fin (2^30)`. `M31Exact` is the prime-field model, while
soundness traces use its embeddings in the extension tower. Source/wire
refinement and account/provenance claims remain separately named obligations.
A field-level theorem alone cannot establish unique raw-byte serialization.

The privacy theorems likewise use K-valued statements and traces (at the
canonical instance, the WideExact field with characteristic p). In
`docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderFieldNormalization.lean`,
`decoded_witness` and `trace_normalization` identify the raw word lift with
its canonical field interpretation. `BuilderRuntimeJoin.lean` explicitly
does **not** require canonical key/owner/salt words; its byte-roundtrip
lemmas need extra `CanonicalWords` hypotheses. Its Rust runtime join remains
uninhabited for the shipped compiler, as D96 records. Thus private witness
words 0 and p can denote the same owner coordinate without contradicting
the privacy statement. That is **not** evidence of two accepted on-chain
public nullifier encodings. The raw withdrawal address and other metadata
are carried/bound outside the algebraic projection; omitting them from a
projection intentionally makes that projection many-to-one, not the parser.

### ASQ8-KANI / P6

Yes: ASQ8 rejects every non-canonical **field** word. It accepts arbitrary
nonzero raw destination/address bindings with high bits because those are
byte identities. The 320-byte parser calls the same payment decoders as ASF8.

Existing exhaustive evidence is
`docs/research/100bit-spend-path-20261013/design/ASQ8-KANI-20261021.md`
and its `evidence/asq8-kani-20261021/` packet. In particular:

- `accepted_request_reencodes_exactly` quantifies over arbitrary 320-byte
  inputs and proves that accepted decoding re-encodes to exactly those bytes;
- `request_decoder_equivalence` covers errors as well as successes;
- `shipped_pipeline_normalization_equivalence` equates shipped decode/encode
  with the extracted fused reference, with no successful-input assumption.

Together with encoder equivalence, accepted byte preservation implies
injectivity of decoding: if two accepted inputs decode to the same full
record, deterministic encoding yields both original inputs, so they are
identical. The existing six harnesses passed with unwind assertions and no
stubs/contracts. This job **reuses** those committed receipts, and does not
claim a fresh Kani or Lean run. Their trusted compiler/solver/extraction
correspondence is P6, not a new Lean axiom. The extracted normalization and
Pool handoff theorems preserve raw bytes; they complement the field-level
soundness/privacy statements rather than changing their semantics.

### Canonicality change / CU estimate

**No additional on-chain canonicality check is needed for the fields audited
here; proposed on-chain change: none; added CU: 0.** No reducing public-field
parser or accepted p-alias was found, so there is no noninjective decoded
field to repair. No patch has been applied.

If the lead separately wants unique **prover witness storage**, a minimal
optional off-chain change is to reject a recipient `owner_key` if
`owner_key.iter().any(|limb| limb.0 >= P)` before record/trace construction.
Apply the same policy to every other raw witness field if a canonical
witness-byte contract is desired. This would reject D96's witness examples;
it is not an on-chain parser fix, and costs **0 on-chain CU**. It is only a
proposal here. On-chain enforcement of private owner word canonicality
would require a relation/design change because those words are not public
wire inputs; this report does not invent a CU measurement for that change.

Limits: source inspection plus deterministic native tests establish the
specific parser/seed result above; only the reused ASQ8/P6 packet provides
exhaustive solver evidence for the complete request codec. We do not prove
global injectivity of cryptographic hashes, arbitrary account byte images,
all witness representations, or complete end-to-end Rust/Lean execution.
No unrelated runtime, adversarial, SBF rebuild or formal manifest replay was
required by this test/document-only change.
