The retained S2 table and regrouping obligations have focused Lean proofs.
This is not yet an extracted implementation theorem for the Rust helper.

`CuSavingsGroups.grouped_eq_reference` proves
the weighted sum over coefficient groups equals the original coefficient sum
for any semiring. `grouped_mask_eq` identifies the mask-weight form under a
cellwise table premise; it requires no nonzero challenge or coefficient.

`emit-s2-tables.py --check` pins the production revision
39c2971dd16c95858a4cfd2c9ae35da052eacfa9 and complete weights.rs,
transport.rs and opening.rs hashes. Its data are the literal 64 group IDs,
12 inactive masks, 64 active-row masks and five-entry TAU permutation. The
Nat model follows the exact five-step row permutation and inactive bit test.
Each named block theorem checks sixteen small ten-bit cells and their row
bounds. Group bounds and source-array lengths are separate theorems. The
complete certificate covers all 1024 cells without native_decide or generated
large-recurrence normalization.

`CuSavingsS2Order` proves that the twelve masks are distinct, identifies each
group's first occurrence and proves their order. `CuSavingsS2Tables.table_correct`
combines the named certificates. Its `grouped_inactive_eq` consumes the actual
table equality to discharge the generic algebra premise.

These proofs were compiled one at a time using the existing local mathlib
4.32 cache in a private Lake workspace. The root checkout was only read; all
generated build objects remain ignored in the side worktree. There was no
dependency build. Each target has command/revision/feature/source/import pins,
exit, wall time, peak RSS, swap and #print axioms evidence. The local runner
applies Lean -M7000 and monitors aggregate descendant RSS with a 7 GiB stop.
All thirteen successful targets pass with standard axioms only, below 1.5 GiB
RSS, zero process swap and less than 2.2 seconds. The first data attempt lacked
the Fin Fintype import; its failed receipt is retained and excluded from the
successful-target audit.

Remaining requirements for this candidate: extract and verify both grouping
helpers, connect the source dynamic search/accumulation order to these finite
tables, bind WideExact arithmetic, and prove unchanged decoding/access/failure
behavior at the actual caller. The Nat row model and semiring theorem do not
silently discharge those machine/source obligations. Whole-verifier
equivalence and soundness/privacy transfer remain open.

The separately archived local finish-context tactic diagnostic found no need
to rewrite the draft's constructor-equality step. Its corrected core-Lean
example is not an Aeneas/verifier component and is not counted in this result.
