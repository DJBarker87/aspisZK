# Stage-2 refactor (2026-10-20)

VERIFIER SOURCE CHANGE under LEAD-DECISION-STAGE2-REFACTOR-20261020.
Stage 1 runtime gates PASS (`7d4c136f0`). Stage 2 Aeneas extraction FAILED; stopped before first facts.

## Changes and extraction purpose

- `finish_relation_round` isolates each scalar fold guard and polynomial update. `finish_relation` spells out the only supported one/two-round cases. This adopts the retained successful finish candidate rather than replaying its failed shared-borrow loop.
- `finish_query_dot` performs the same ordered dot pushes through indexed shared slices, avoiding the accumulator iterator borrow. It retains the original error mapping and trace order.
- `resume` replaces the mutable Reader/from_fn capture with a fixed 22-element indexed read. All cursor updates, validation, decoding and digest comparisons retain their order.
- `tx2_common` moves the accumulator fields out after the query loop, finishes the standalone weight vector, and reconstructs the accumulator. This avoids borrowing the partially borrowed whole accumulator after finishing its weights. No new allocation or field arithmetic is introduced. This change is insufficient for the pinned translator: Aeneas rejects the final `&a` borrow at candidate.rs:237. `Variant::folds` is 1 only for S1 and 2 for S2/D, so the explicit cases cover every existing variant. The reader loop visits the same 22 positions as from_fn. Moving/reconstructing the Vec changes no payload, allocation, observer or digest call; pending owns its separate residue buffer.

`compact.rs` and `multiproof.rs` remain byte-identical. Default Pool and registry ids remain `[0x41;32]` and `[0x44;32]`; the deployment-constant change is absent from this branch base.

## Gates and artifact

All required runtime gates passed, including 8/8 P_R1 plus a verified retry loop and all six per-fixture B1 criteria. See `../evidence/stage2-refactor-extraction-20261020/REPORT.md`, manifest and receipts for results and retained staging failures. Rebuilt verifier: SHA-256 `0622ad3f19b81d71776f1a0b2fdb624cca3f371c7c4bccb14adc8ea1dfbc8090`, 1,403,912 bytes. Strict stack audit passed against the complete linked ELF.

## Open

R13/R12 source/model/Checks refinement, concrete arithmetic and Merkle backends; R15 authenticated checkpoint provenance and skipped-value canonicality; R19 all-input oracle/first-read bound; S8 re-pin and analytical CU bound on this verifier. Runtime differential evidence does not establish universal formal source equivalence. Charon produced valid LLBC (SHA `1bb25f41…8df5`), but pinned Aeneas exited 2 at `candidate.rs:237:20–237:22`: “There should be no bottoms in the value” (`interp/InterpExpressions.ml:55`). The runtime-gated source is retained as a candidate; no successful whole-cone translation or generated Lean is claimed. Per the mandate, no replacement refactor was attempted after this gate failed. All three first facts remain obligations.
