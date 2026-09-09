**Experimental application and authentication contract — version 1**

This is a public message inbox attached to a real Aspis private transfer. A is the selected output lane of the existing eight-lane Aspis Pool, identified by `(Pool master account, selected lane account)`. Its application root is `lane.tree.root`; its sequence is the pair append index. The master and checkpoint authenticate the pool identity and retained historical membership anchor. This transfer updates the selected lane and lane history; it does not advance the global checkpoint root. B is a different, depth-20 SHA-256 accumulator account owned by the experimental inbox program. Neither root is a STARK C1/C2 commitment.

A is owned and updated by the pinned Aspis Pool program. Its transition consumes one source nullifier, verifies a selected forest membership/payment/append proof, appends the recipient/change pair and updates the relevant history page. The source note's old commitment can remain in the append-only tree: the permanent master-scoped nullifier prevents spending it again. The genuine fixture spends 1,000 into 600 recipient plus 400 change, with the existing private-transfer asset and fee rules. Both outputs are ordinary A outputs. B records an attestation to this transfer and **credits no value**. Its recipient identifier is the proof-bound recipient note commitment, not a new public wallet address. Nothing in this experiment moves either output's value into B.

B is permissionlessly initialized at the unique PDA
`PDA(B_PROGRAM, ["aspis-v8-inbox-v1", master_pubkey, asset_u32_le])`.
Initialization checks the canonical Pool-owned master, its asset and master PDA, the system-owned empty destination, payer signature and privileges. It funds only missing rent, then uses signed System allocate/assign CPIs. Its one-use update authority is the checked transaction choreography below. B exposes no close, reset, arbitrary root write or administrator update instruction. The owner/program identities are separate; B never writes Pool-owned data. Production dispatchers and release registrations are unchanged.

**Execution and replay rules.** The successful transaction contains these top-level instructions in this order:

| Index | Owner invoked | Action |
|---:|---|---|
| 0 | B | `ATH8`: authenticate identities and the exact three-instruction choreography; check live A and B old roots/sequences |
| 1 | A / Pool | Original `ASQ8`; unchanged Registry/account checks, `ASF8`, verifier CPI, authenticated `ASR8`, nullifier and lane/history settlement |
| 2 | B | `ATF8`: authenticate the same choreography and B state; check the canonical Pool marker and new lane sequence; derive receipt and verify empty-slot insertion; write B |

B reads the runtime-authenticated instructions sysvar. It requires the expected current index, exact Pool program at index 1, exact embedded 320-byte ASQ8, the complete original source account metas, and identical B pre/final bytes apart from the four-byte phase magic. Both B instruction account lists must exactly match the actual privileges. Every role account is distinct. A missing or altered phase rejects. Any later failure fails the transaction. The source instruction omits B from its accounts, preventing an intervening B write. There is no persistent prepared state or partial-success status.

The first attempted design called Pool by CPI and was rejected by `CpiInvocationForbidden` (`0x41532036`). The retained design preserves that intentional top-level guard. Each owner updates its own accounts through its own authorized entrypoint. The original Pool still CPIs into the verifier and System program. There is no coordinator writing a foreign root directly.

B does not consume cross-instruction return data as a verification certificate. A successful index 1 is necessary to reach index 2. The pinned Pool itself authenticates the expected verifier's exact 792-byte ASR8 and its binding to the attempted ASF8. At index 2, B additionally decodes the Pool-owned nullifier marker, checks its canonical PDA, master/nullifier/domain/profile/release/transition/anchor fields, reads the live lane root, and checks sequence `a+1`. Thus caller-supplied roots or a result double cannot supply the positive acceptance result.

The Pool master/anchor/lane are independently authenticated by the existing source path; B's owner, length, header, asset, master, PDA, sequence and root are independently authenticated by B. Lane sequence/root are read at offsets 88/96 of the exact 768-byte lane encoding. The Rust helper's historical “in its CPI” comment refers to canonical Pool validation; in the retained route Pool is top-level. The precheck snapshot is tentative until that exact Pool instruction succeeds. The driver compares it with the full typed encoder/decoder. This offset check is not a formal Rust/SBF refinement proof.

Nullifier scope is `(source master, source nullifier)`, with PDA seed `aspis-pool-nullifier-v1`. It never incorporates B or a destination domain. Exact replay with a new blockhash rejects; refreshing roots cannot erase the occupied source marker; choosing another destination cannot authorize another consumption. B has one route per master/asset and no alternate-destination selector. Existing source marker permanence remains part of the inherited contract; plan-account cleanup does not close nullifier markers. We tested occupied-marker System reallocation and B reinitialization. An ordinary standalone A transfer remains supported; this extension requires atomic B insertion only for its declared three-instruction handoff route.

**Canonical encodings and field provenance.** Integers below are fixed-width little endian; identities are 32 raw public-key bytes; Aspis digests use its canonical decoder/encoder, and SHA-256 roots are raw 32-byte strings. No variable-length concatenation ambiguity is introduced.

Let `D = "aspis/research/v8/atomic-message/v1"`,
`R = SHA256(D || "/release:pool-asq8:sha256-depth20:message-only")`,
`E = SHA256(D || "/empty")`, and
`Node(l,r) = SHA256(D || "/node" || l || r)`.

The receipt is:

```
H = SHA256(D || R || B_program || Pool_program || verifier_program
           || master || selected_lane || proof_account
           || a_sequence:u64 || A_old || (a_sequence+1):u64 || A_new
           || B_account || b_sequence:u64 || B_old || exact_ASQ8[320])
```

B's new root is deliberately absent from H to avoid a circular definition. It is uniquely checked as the depth-20 empty-slot replacement at index `b_sequence` with leaf H. The same 20 siblings must reconstruct B_old from E and B_new from H. Sequence must be less than `2^20`. This binding is an execution rule; hashing B fields after source proving does not make them part of that proof.

| Fields | Binding/check |
|---|---|
| Source protocol, transition kind, profile/release, Pool program, master/domain, retained anchor root/sequence, nullifier, asset, recipient/change commitments | Existing canonical 320-byte ASQ8; authenticated 1,880-byte ASF8 and complete-attempt proof binding |
| A lane identity, before frontier/root/index, candidate afterstate/root/index, checkpoint and full authoritative source context | Existing ASF8 constructed/checked from live accounts; checked again by Pool at settlement |
| Verifier and immutable proof-storage account identity | Existing `complete-attempt/v1` digest, profile/release binding, ownership/seal checks and Registry entry validation |
| B program, version, release, master/asset route | Explicit B constants/header, canonical account/PDA and source identity checks; included/derived in H |
| B old root/sequence, new root, path and H | Fresh live B check and deterministic empty-slot insertion; **not ZK-proved** |
| A old root/index copied in the envelope | Exact live precheck; source ASF8 independently binds the same transition; checked new index/root feeds H |
| Recipient / payload | ASQ8's recipient and change commitments are the existing payload; H includes the exact ASQ8. No unrelated source field is repurposed |
| Amount, additional asset credit, B fee | No B balance or fee field exists; no B value credit. Source amounts are private witness values subject to the inherited payment relation |

The original research `complete_binding.rs` supplies the profile/release and attempt domain; this experiment changes neither transcript nor relation. The B release identifier describes this ABI and must be used with the measured B ELF hash. It is not a magical attestation to arbitrary upgraded code. Pinned program code, the Registry release policy, Solana program ownership/executability, and instructions-sysvar integrity remain explicit trust/coupling obligations.

B account data has exactly 116 bytes:

| Offsets | Content |
|---|---|
| 0..8 | `BIX8`, version 1, depth 20, two zero reserved bytes |
| 8..40 / 40..44 | source master / asset |
| 44..52 / 52..84 / 84..116 | sequence / root / last H |

Each pre/final instruction has exactly 1,112 bytes:

| Offsets | Content |
|---|---|
| 0..8 | `ATH8` or `ATF8`, version 1, depth 20, two zero reserved bytes |
| 8..16 / 16..48 / 48..80 | B sequence / B_old / B_new |
| 80..88 / 88..120 / 120..152 | A sequence / A_old / H |
| 152..792 / 792..1112 | 20 siblings / exact ASQ8 |

`ABI8` initialization is exactly 44 bytes: its eight-byte version/depth header, master and asset. Unsupported operation kinds, noncanonical/reserved/trailing data, wrong privileges, wrong owners/PDAs, role aliases, stale roots/sequences, full B, wrong insertion paths, invalid or unsealed/substituted source proofs, or unexpected verification results fail. Missing data and malformed encodings are errors, not fallback roots.

**Model versus tested enforcement versus cryptography.** `model.py` was written before the on-chain path. Its `VerifiedSource` is an explicit premise representing a source transition authenticated by the intended verifier; its fields must correspond to the decoded canonical ASQ8/ASF8. The pure transition checks freshness, routing and global one-use markers, computes the same message receipt, and returns an entirely new state only after both operations pass. It proves nothing about the verifier merely by accepting that premise. Random sequences check the model's all-or-nothing and one-use invariants; nine real SBF results are differentially compared with its independent sparse-tree reconstruction. No Lean theorem, new axiom, retained sorry, or Rust-to-Lean/SBF refinement claim is introduced.

For the tested runtime, failure snapshots include Pool master/checkpoint, selected lane, current/rollover history, nullifier marker, Registry and entry, proof account, and B. Every failed case compares owner, executable flag, lamports and data exactly. Payer transaction fees are tracked separately. There is no persistent settlement receipt outside the Pool's marker/state and B's root/last-H; all of these revert on failure.

Cryptographic acceptance remains conditional on the inherited V8 obligations described in README and the Milestone-II assessment. New obligations include B hash binding/domain separation, correct interpretation of the canonical source result, fixed code/release authority, path implementation correctness, transaction introspection and runtime atomicity. Tests supply evidence for these interfaces, not a numerical probability for Rust/compiler bugs.

**Usability and privacy.** B is an immediately authenticated inbox receipt; it has no spend or execution method. A later consumer would need its own explicit processing semantics. The root alone does not provide the receipt history or a next insertion/membership witness. Clients need the ordered H leaves and corresponding transaction data (or a maintained authenticated path). A's recipient still needs the existing note opening/key/salt and the relevant forest/lane updates to reconstruct its spend witness. This prototype offers no data-availability service or sequencing mechanism.

The transaction reveals both participating accounts, roots and their association, both sequences, H and B's path, proof-account address, public source nullifier/asset/anchor, and recipient/change commitments. There is no new public amount scalar, but the published synthetic fixture is known to be 1,000 = 600 + 400. H binds commitments, not a public disclosure of those private values. Omitting witnesses from instructions does not establish unlinkability or full-view ZK. The 20 SHA path rounds and H computations are public and deterministic.
