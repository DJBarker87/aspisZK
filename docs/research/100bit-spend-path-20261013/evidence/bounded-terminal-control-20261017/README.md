# Bounded source control for the terminal proof

`BoundedControlCarry.bounded_carry_is_digestCarry` (namespace `AspisBoundedControl.Carry`) proves actual extracted candidate loop success for every u64 and equality to the existing `R0P.digestCarry`, including its twenty-level bound. Its proof uses a symbolic fuel invariant and bit-vector primitive facts, not enumeration of all u64 values. `BoundedControlAmount.some_agrees_with_old_closure` proves actual explicit-match candidate behavior agrees with the retained old amount-check closure; `false_implies_range` derives the canonical scalar bound. No unknown intrinsic result, Option-method implementation, carry value or intermediate success is assumed by these theorems.

The minimal no-std Rust candidate was extracted with pinned Charon built MIR (`--preset aeneas`, two selected entrypoints) and Aeneas (`-loops-to-rec`). The emitted Lean file is retained byte for byte as `BoundedControlSource`. No generated-source substitution or new external declaration was added. The initial extraction omitted the required preset and was rejected; the next emitted i32 shift amounts incompatible with the pinned Lean wrapping-operation API. Changing the Rust shift RHS literal types explicitly to u32 fixed the mismatch at source, followed by re-extraction and compilation. Those failed diagnostics are retained separately. The old amount closure proof is reused directly.

`candidate/proposed-source.patch` is a reviewable candidate for eliminating four capped trailing-ones calls and one `Option::is_some_and` call in the production terminal source. It has NOT been applied. The minimal helper proof does not assert that the entire modified crate or deployed program was extracted, nor prove compiler correctness or equality of released binaries. Full candidate integration, source correspondence and runtime cost remain open. The existing original intrinsic itself still has no proved extraction model; the proposed replacement is proved against the protocol's retained bounded-carry model.

Native release tests on the exact new candidate hash passed: 4,194,304 capped-carry comparisons (all twenty low bits, four upper-bit patterns) and boundary/deterministic amount-guard comparisons. These support development equivalence with the old Rust operations; the universal statement proved in Lean is candidate execution equals `R0P.digestCarry`, not an unmodelled std intrinsic theorem. The updated native receipt records 0.201 seconds controller wall, 122,784 KiB process peak RSS, zero swaps, and in-run 4/6 GiB memory/swap-zero scope limits. It is distinct from the older source's native run.

Focused Lean targets ran under 4/6 GiB caps with swap disabled and no dependency rebuild. All theorem reports contain only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Source-only targets have no theorem reports. Receipts pin exact source/object/import hashes, toolchain, commands, source revision, timing and resource usage. Their runner `source_base_revision` identifies the pinned proof workspace; the new Rust candidate is identified by its separate source hashes. No complete frozen-manifest replay or accepted-spend security claim is made here.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `BoundedControlSource` | 2.152 | 2600900 | 0 |
| `BoundedControlArithmetic` | 1.83 | 3779608 | 5 |
| `BoundedControlCarry` | 1.59 | 3791200 | 2 |
| `TerminalAmountGuardClosure` | 1.153 | 2590100 | 1 |
| `BoundedControlAmount` | 1.514 | 3782988 | 2 |
