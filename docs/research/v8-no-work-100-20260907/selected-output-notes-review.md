# Decoded recipient/change fields open the recorded output notes

Research pin: `e90e7338656f221c9a1bbde90d533ba94d002014`. This is the next deterministic payment slice after [strict decoded amounts](selected-amount-endpoint-review.md), not a new parameter or security survey. No production, Rust, masking, transcript, verifier-default or proof-body change is made.

## New endpoint and prerequisites

`SelectedOutputNotes.lean` constructs the exact recipient/change owner, amount and split-salt fields read by `recovered_witness::decode`. From individual three-block sponge residuals, source carry aliases, required final-chunk zeros and literal public bindings, it derives:

```
public recipient commitment = noteHash(decoded recipient owner,
                                      decoded recipient value, public asset,
                                      decoded recipient salt)
public change commitment    = noteHash(decoded change owner,
                                      decoded change value, public asset,
                                      decoded change salt).
```

The three round chains are constructed from the eleven two-round transitions per block. They are not supplied as premises. The field values and the natural value are read from the **same arbitrary table**; there is no honest-trace equality, decoder-success, compiler-acceptance, valid-witness or already-correct-hash hypothesis. The raw-coordinate corollary proves that canonical note cells yield the same decoded fields and that digest representatives have not been silently changed by modular reduction.

The public asset and two commitments are independently supplied inputs whose explicit binding residuals must vanish. This theorem does not authenticate those inputs, derive their authority from prover-supplied columns, or replace the outer caller/account/runtime/settlement context checks. It also does not prove that complete verifier acceptance enforces the individual residuals.

## Exact selected cells and source

| Field/boundary | Recipient | Change |
|---|---|---|
| Sponge blocks | 27,28,29 | 30,31,32 |
| Initial domain/length row | 432 | 480 |
| Decoder owner key | row444, columns0–7 | row492, columns0–7 |
| Decoder amount | row460, column0 | row508, column0 |
| Asset binding | row460, column1 | row508, column1 |
| Salt limbs0–5 | row460, columns2–7 | row508, columns2–7 |
| Salt limbs6–7 | row476, columns0–1 | row524, columns0–1 |
| Required zero tail | row476, columns2–7 | row524, columns2–7 |
| First full-state carry | row443→448 | row491→496 |
| Second full-state carry | row459→464 | row507→512 |
| Final digest/public binding | row475, columns0–7 | row523, columns0–7 |

`recovered_witness.rs:53–57` defines the exact generic note helper; the transfer return uses `note(27)` and `note(30)`. The source `pool_v1_note_commitment` uses the owner/value/asset/salt framing; the maintained mathematical `noteHash` uses domain `0x41530003`, length18, rate-eight chunks `[owner0..7]`, `[value,asset,salt0..5]`, `[salt6,salt7,0,0,0,0,0,0]`.

The four full-state carry records are frozen copy tags1124073475–1124073478 in `pair_forest_copy_terminal_constants.rs`. Recipient tags3475/3476 are transfer-only; their weight is one in this transfer slice. Change tags3477/3478 are unconditional. All use the complete16-lane identity pattern with zero offsets. The forest relocation preserves these sponge rows. The host schedule writes the carry residual in the opposite orientation (`consumer-producer`) to the copy registry; both vanish on precisely the same equality. This leaf consumes the registry orientation through the previously proved `absorbed_from_carry` interface, not an assumed sponge chain.

`pair_constraint_residuals.rs:298–327,347–366` supplies the host initialization/carry/zero schedules. The compiled counterparts are `pair_forest_semantic_terminal.rs:219–314`: block27's domain/length and chunk schedules are enabled by the transfer branch, block30's are common. Public digest bindings occur at615–650, and the recipient/change asset equations at1164–1177. The twelve final rate-chunk zeros are **required schedule cells**, not the relation-free mask registry. Other high-lane absorption zeros remain checked in the source, even where this sufficient hash predicate does not require them.

## Reused proof interfaces

| Declaration | New use |
|---|---|
| `SelectedNoteRecovery.blockRoundChain` | Constructs each of the six block chains from explicit row-pair residuals, using the maintained two-round conversion. |
| `absorbed_from_initial`, `absorbed_from_carry` | Transports the literal domain/length initial states and actual carry equalities. |
| `HashMerkleModel.sponge3_forces` | Reuses the established deterministic three-block sponge statement. No old work-normalised security bound is used. |
| `first_chunk_is_decoded`, `second_chunk_is_decoded`, `third_chunk_is_decoded` | Proves the actual owner/value/split-salt chunk identities, using tail constraints only for the required zeros. |
| `decoded_output_opening`, `public_output_opening`, `both_transfer_output_openings` | Derives both output hash openings and transfers literal asset/commitment residuals to independently supplied public values. |
| `note_cells_of_canonical_table` | Derives all note-helper canonicality premises from the full bounded 1024×16 canonical C1 precheck, proving the actual owner/amount/salt addresses are in range. |
| `canonical_decoder_fields`, `canonical_digest_representatives`, `raw_public_output_opening`, `both_raw_transfer_output_openings` | Connects canonical raw note cells to the same field/natural decoded record and both public openings. The final theorem derives the local canonicality premises from the bounded full-table precheck. |

The new record `NoteFields` is a literal field/natural decoder view, **not** a `PaymentWitness` subtype whose validity is assumed. The shape/canonical checks of the full Rust decoder still precede that field view. `CanonicalNoteCells` states canonicality only of the helper's actual owner/value/salt reads; the new bounded-address theorem derives it from the full 1024×16 canonical precheck. Conversely, local canonicality does not imply unrelated table cells are canonical or that path/occupancy parsing succeeds.

The inherited round predicate still uses `gateStep(rc)` and explicit `RoundConstants`. Equality to `poseidon2::evaluate_trace_round_pair`, concrete compiled constants, field-machine kernels and automatic Rust translation remains an open source interface. The new theorem is a modeled residual-to-output-opening result, not a completed literal Rust validator endpoint. The amount bounds/positivity/conservation result from the preceding leaf is retained without repeating it; this hash leaf does not manufacture positivity from a hash identity.

## Focused evidence

Status: **formal proof complete for the stated modeled residual/decoder endpoint**. The focused check passed at the research pin above. The runner uses pinned cached Lean4.32.0 and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, verifies imported source/olean provenance and compiles only the new leaf under `-M7000` plus the7,340,032-KiB aggregate process-tree RSS guard. Jobs are root-serialized. No dependency, Rust or SBF rebuild was performed.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_output_notes.sh \
  docs/research/v8-no-work-100-20260907/experiments/selected-output-notes-v1.log
```

The exact command and cache/source audit are recorded in [selected-output-notes-v1.log](experiments/selected-output-notes-v1.log): exit **0**, **21.22 s** wall time, **5,541,314,560 bytes** peak RSS, **0 swaps**. All twelve `#print axioms` checks report only the standard `propext`, `Classical.choice`, `Quot.sound` subset; the first chunk identity is axiom-free. No `sorry` or new axioms were introduced. The only diagnostic is a harmless unused-simp-argument warning; the green source was not changed or replayed just to suppress it.

- Lean source SHA-256: `e7a51e542c33f0c90db5330d43ad02d3dbe405e4c89cd1f01f02e30963e9b2bb`.
- Checked olean SHA-256: `00da269fe397e50fcefc17623ebc012a7e8fc3bd081390b67e157f861e41982a`.
- Toolchain: Lean4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, arm64 macOS.

The inherited V7 gate/occupancy oleans were previously exported from their pinned source; their exact hashes and all recursively imported repository-source identities are checked by the runner. Other imported repository oleans match the pinned shared cache. No concurrent main changes or dirty imports were consumed. No real owner key, salt or witness is evaluated or printed.

## Remaining endpoint

This closes the recipient/change note-opening slice left explicit by `selected-note-recovery-review.md`. Combining it with the existing owner/input-note/nullifier, path, occupancy and strict-amount lemmas still requires a coherent source residual predicate, canonical decoded trace, literal compiler/hash interpretation, and authoritative public/runtime/settlement context. Output-pair occupancy/append/transition linkage is not proved here; withdrawal coverage is not inferred.

Upstream accepted-extraction failure, authenticated/replay access, early C1 causality and Fiat–Shamir resources remain separately accounted for. No new probability term or numerical security claim follows from this deterministic theorem. The proof body stays **40,282 bytes**, with no new verifier operations or public messages. Full-view privacy and matched complete-transaction CU are unchanged obligations; proof-check resources are not prover or verifier benchmarks.
