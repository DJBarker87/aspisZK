# Public affine correction producer

Parent inspected: `7e947e6a983d3e079ca67217bd9753351a398b7a`.
New leaf: `lean/SameBodyPublicCorrection.lean`.
SHA256: `59a1b2c9723b7e5df68c5ce9af18dba429179f6eab40f9afce082a9473e6c0e1`.

This closes the previously omitted **deterministic expression producer** for
the two public entries and their affine correction. It does not construct
the entire ordinary functional, image challenge or ideal accepted execution.

## Actual public inputs

Only original weight entries 0 and either 1 or 2 occur in this correction.
All lie in row group zero. The actual compiled arrays give
`INACTIVE_ROW_GROUPS[0]=0`, `INACTIVE_GROUP_MASKS[0]=59391`; bits0,1,2 of that
mask are one. `first_mask_bits` proves this finite fact. Consequently no whole
mask table, supplied mask value, or prover-supplied weight digest enters this
constructor. No omitted mask assumptions are needed for these three entries.

The three point rows are constructed from `z` by literal source operations:
the carry loop at coordinate9 then8..0 and XOR at coordinates7 and6. Arbitrary
field coordinates are permitted; Booleanity is not assumed. The shifted row
scales are inherited from `SameBodyOrdinary`.

`entry` implements the reference `Description::entry` for indices0/1/2.
`pair` implements selected `v8_shared_weights` `Description::entry_pair`:
target8 for x, target9 for y, accumulating common factors then common-minus-
right and right. `correct` calls same-word OOD preparation and uses that
computed pair in the literal sequential subtraction
`claim - intercept*pair[0] - slope*pair[1]`.

`correction_constructed` proves the preparation, pair and corrected scalar are
computed, not freely supplied. `correction_preserved` proves every legal later
relation serialization preserves this output (including coordinate-inverse
failure) at fixed earlier challenge inputs. Those challenge values still need
actual transcript producers.

## Evidence and limits

Focused command in `lean/`:

```
LEAN_PATH=. lake env lean -M1800 -o SameBodyPublicCorrection.olean SameBodyPublicCorrection.lean
```

Lean4.33.1, exit0, wall0.40s, RSS688,390,144 bytes, swaps0. Three promoted
declarations print only `propext`/`Quot.sound`. Local cached first-party imports
are the preceding checked continuation leaves; no historical Mathlib/V8
artifacts are imported. This is not another clean closure rebuild or fresh
kernel replay. Parent's focused build manifest will supply that provenance.

Executable guards pass64 F17 comparisons of the shared pair against separate
reference entries, including zero kappa/coordinates; they also retain inverse
failure and constructive nonvacuity. These are small-field model checks, not
actual Rust tests or universal equality of optimized field kernels. A first
failed leaf had missing pair-state type annotation and a rewritten equality
proof using a stale hypothesis; both were fixed without changing statements.

Remaining source boundaries:

- The frozen constant source identity is checked by inspection/hashes, not a
  Rust operational extraction theorem.
- Equality of the shared pair and reference entry functions for all actual
  QM31 inputs remains a field-arithmetic refinement; tests are not that proof.
- Arithmetic operations and inverse semantics are still explicit interfaces.
- `z`, gamma, kappa and both OOD points still need source-transcript coupling.
- Entire mask table, transported terminal functional and image-tau framing
  remain later producers; this leaf needs only group-zero bits, not all masks.
- No payment or authentication acceptance, resource probability, ZK or CU claim.

Source hashes:

| File | SHA256 |
|---|---|
| pair_forest_copy_terminal_constants.rs | cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50 |
| pair_forest_copy_terminal.rs | 50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5 |
| v6_transcript.rs | 48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf |
| structured_weights.rs | 06befd20c084234ce1afa2d7cf3612a12370fdb0e98e95db30d89cf245b51089 |
