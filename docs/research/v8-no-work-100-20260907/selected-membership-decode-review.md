# The decoded UInt32 index follows the recorded pair/forest path

Source pin: `503332fbe747db381fc8ee67c4bbdd3631ec97cf`, inspected clean before this continuation. No earlier green proof or Rust/default source is changed.

## The missing representation bridge

The existing [selected path](selected-forest-path-review.md) already proves all24 modeled hash steps and their recorded endpoint. The missing piece was not another hash-chain theorem: `recovered_witness.rs:47–66` stores the first direction separately, assembles the next20 into a `u32` index using OR/left shifts, and stores the final3 as booleans. The validator follows those reconstructed representations, not an arbitrary separately supplied24-direction vector.

Two focused leaves connect them:

- `DecodedIndex32`: the exact OR/shift recurrence over both Nat and **Lean UInt32**, with a symbolic proof that every prefix `n≤32` agrees numerically. Every intermediate shifted bit fits and the shift count is below32. At20, the index is below `2^20`, its first20 bits are exactly the supplied direction bits, and every higher bit is false.
- `SelectedMembershipDecode`: individual selected bit residuals plus canonical raw C1 imply the literal raw parser returns0/1 booleans on all24 path rows. The same booleans select the exact raw sibling reads and assemble the index above. Existing selected node/copy residuals then construct the decoder's **1 pair +20 lane +3 forest** path and its row907/public-root binding.

No successful decoder, honest trace, expected witness, correct root or arbitrary desired index is assumed. The table can be malicious; source residuals and bounded canonicality are explicit prerequisites. This is a deterministic representation/semantic interface, not proof acceptance enforcing those prerequisites.

## Actual reads, order and root boundaries

The source row formula is `aux(level)=913+16*(level/4)+4*(level%4)` for `level<24`. The earlier selected layout theorem proves those reads, including the adjacent child row, fit the1024-row table. The new canonicality proof uses that bound rather than reading a default cell outside the table.

| Source segment | Decoder representation | Recorded hash boundary |
|---|---|---|
| Level0, direction row913 | Separate `selected_second`; pair commitments are row914 c0–7 and c8–15 | Pair hash row75 = boundary1 |
| Levels1–20, direction rows917…993 | `index |= (bit(i+1) as u32) << i`;20 siblings | Lane root row395 = boundary21 |
| Levels21–23, direction rows997,1001,1005 | Three separate booleans/siblings | Forest root row907 = boundary24 |

The raw sibling helper reads the unselected child from `aux(level)+1`: c0–7 when the direction is true and c8–15 when false. Canonicality of every decoded sibling limb follows from the full bounded1024×16 precheck, so field reduction cannot silently substitute a different raw digest.

`pair_forest_trace.rs:91–105` starts its lane-root loop with the checked pair-leaf hash and follows exactly20 bits of the decoded index. `relocate_and_extend` appends the three forest siblings in increasing order and compares the resulting root with the global public anchor. The compiled public binding is row907 (`56*16+11`) in `pair_forest_semantic_terminal.rs:615–622`. The new theorem takes that literal residual, not a premise that its computed root already equals the expected root.

## Reused V7/selected proofs

The old V7 range-bit decoder is not repurposed as a20-bit index proof: its30-bit amount reconstruction is a different shape. The new generic UInt32 proof instead uses the pinned Lean bitwise semantics (`toNat_or`, `toNat_shiftLeft`) and symbolic Nat bit laws.

The dependent leaf reuses the actual selected24-level path, V7 gated-child ordering and deterministic `foldl_chain` twice, at the20- and3-level boundaries. It does not unfold a24-level concrete recurrence. The first boundary is identified with the actual decoded input-pair commitments, not merely with an existential sibling.

`same_raw_input_pair_checked` consumes the existing occupancy/copy theorem on the same raw table and identifies its selected side with the now-proved raw parser result. `same_decoded_note_nullifier_and_anchor` composes the already proved owner/input-note/nullifier equations with the same raw membership path: the chosen pair commitment is the note opened by the decoded key/amount/salt, the public nullifier is derived from that same key/salt, and the decoded forest path reaches the explicitly bound public root.

## Remaining source and authority boundaries

The generic index result is a checked **Lean UInt32 operation model**, not an automatically generated Rust-to-Lean translation. The source loop's identical operation/order and legal shift bounds are identified explicitly; compiler/FFI translation remains a separate boundary. The exact raw bit `Option` branch and same-table sibling equations are proved, but this is not one theorem returning the full Rust `PoolV1PairForestPrivateTransferWitnessV1` record.

The path/owner/note/nullifier proofs still use the maintained `gateStep(rc)`/hash model. Concrete Rust Poseidon round evaluation/constants and field operations must be connected. The raw pair checker is the already proved field-stage model, including selected-slot spendability; actual raw canonicality and parser/source translation remain explicit. The independent public asset/nullifier/anchor parameters do not establish runtime authority: outer pool/deployment/sequence/asset/root checks, spent-nullifier context and the final settlement transition are not supplied by prover columns.

The decoded amounts, input/output notes, occupancy, output pair and selected path now have modeled deterministic slices. They should not be called wholly open. Their unified literal validator/source endpoint and the late snapshot/frontier append remain to compose. Accepted-proof→constraints/recoverable-C1, replay/extractor resources, Fiat–Shamir and full-view privacy are separate obligations. No new probability bound, proof-body value or verifier operation is introduced; the body allowance remains **40,282 bytes** and there is no new CU/prover benchmark.

## Focused evidence

Generic `DecodedIndex32` is **kernel-checked**. The first attempt failed only on compressed syntax in the final20-bit corollary; all generic recurrence/UInt32 lemmas already elaborated. Adding explicit Nat binder types and spaces closed the corollary without a semantic or resource change.

| Generic check | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| [v1](experiments/decoded-index32-v1.log) | 1 | 27.06 s | 5,448,122,368 B | 0 |
| [v2](experiments/decoded-index32-v2.log) | 0 | 15.62 s | 5,568,364,544 B | 0 |

All seven final generic audits use only the standard `propext`, `Classical.choice`, `Quot.sound` subset. No `sorry` or new axioms occur in retained source. The failed elaborator's temporary `sorryAx` is confined to the rejectedv1 diagnostic.

Generic source SHA-256: `1c0d87d8ead8f5e326af7d9ca8b89595e13819ea0f4f39d9029255c3004276b7`.
Generic olean SHA-256: `4fb1dd451472ef50d7d9d7c3d705608ade593dc4af0584131ffa628e445628d3`.

Dependent `SelectedMembershipDecode` is **kernel-checked for the stated modeled source/residual endpoint**. Its fourteen final axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`; there are no added axioms or `sorry` in retained source.

| Dependent check | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| [v1](experiments/selected-membership-decode-v1.log) | 1 | 28.78 s | 5,435,375,616 B | 0 |
| [v2](experiments/selected-membership-decode-v2.log) | 1 | 20.33 s | 5,453,889,536 B | 0 |
| [v3](experiments/selected-membership-decode-v3.log) | 0 | 22.91 s | 5,583,601,664 B | 0 |

The dependent failures were function-level proof glue, not counterexamples: raw sibling read definitions were partly applied; digest start-zero/truncation needed pointwise equalities; overloaded Fin24 zero did not rewrite as a literal Nat zero. The replacement uses explicit pointwise equalities and `⟨0, proof⟩`, leaving every original theorem statement and prerequisite unchanged. No supplied path/root equality, increased resource cap or unchanged replay was introduced. Temporary `sorryAx` in failed diagnostics is absent from the final source/audits.

Dependent source SHA-256: `cc91edd69fdbfb023b16ba443e7cfc0b6657cd272565a82a10ed2546a5addad2`.
Dependent olean SHA-256: `30d16ee5b6add0867901de13e8a4bdc49c2007de7a3fe60682559dd57305a6f2`.

Both runners reuse pinned Lean4.32.0 (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`) and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, with the7,340,032-KiB aggregate process-tree RSS guard and Lean `-M7000`. No cold dependency, Rust or SBF rebuild was performed. The dependent runner verifies source/olean hashes against the selected cache and the generic leaf's green evidence. The exact source revision, commands and old/new hashes are recorded in the logs. All builds were serialized under explicit root slot grants.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_decoded_index32.sh \
  docs/research/v8-no-work-100-20260907/experiments/decoded-index32-v2.log
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_membership_decode.sh \
  docs/research/v8-no-work-100-20260907/experiments/selected-membership-decode-v3.log
```

These are the archived exact commands; the runners require a fresh evidence filename for any justified changed-source rerun. No real key, salt or witness is evaluated or printed.
