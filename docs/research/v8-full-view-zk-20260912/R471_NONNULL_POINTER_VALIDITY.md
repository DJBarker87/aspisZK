# R471: NonNull validity prerequisite

Target: `AspisV8R19/R471NonNullPointerValidity.lean`.

The pinned Lean 4.32 focused build exited 0 in 1.28 s, with peak Lean-child
RSS 2,542,876 KiB and zero swaps. Source revision:
`6e1f354487f8e7e3ebd3c2002c361199d1d3630b`. Target SHA-256:
`75c175434f54e30fb47cdaf595a2d80ffd4d6e76d94bac90800ff14e51919997`.
Complete source, log, receipt, all 13 axiom reports, and the two preceding
local theorem-error attempts are saved in `evidence/r471-nonnull-pointer-validity/`.
Successful declarations use only `propext` and `Quot.sound`, or no axioms.
The failed attempts are retained as failures, not proof evidence.

The explicit R432 allocation fragment now has a validity-checking NonNull
conversion. It succeeds exactly for nonzero addresses, rejects zero regardless
of provenance, and retains the entire pointer, including allocation origin.
The two conversion directions compose to the identity on valid pointers.
Successful addition preserves a positive address. Consequently every successful
modeled iterator construction from a nonzero start has two valid cast endpoints.
This includes empty slices with nonzero dangling pointers and all backed
endpoints, including the one-past endpoint. No allocation is required for the
empty dangling case.

This is a prerequisite in the explicit allocation fragment, **not** Rust/LLBC
pointer semantics, an actual-source iterator theorem, or a privacy/soundness
result. It does not replace the R433 constructor's unchecked casts. The first
remaining proposition is that the actual R440 Fun70 raw-const-pointer to
NonNull transmute preserves this complete pointer representation and satisfies
the target validity condition for the actual constructor-produced iterator.
The actual safe-slice input relation, provenance and lifetime bridge, loop
pointer operations, and whole freeze extraction remain unproved.

Source location for the first live cast in input SHA-256
`96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48`:
`translated.fun_decls[70].body.Structured.body.statements[9].kind.Switch.If[2].statements[3].kind.Assign[1].UnaryOp[0].Cast.Transmute`.
The operand copies local 8, raw pointer type 4178, to NonNull type 4176.
The captured NonNull declaration 58 has a single `pointer` field with a
`NotNull` pattern. The standard-library span is `slice/iter/macros.rs:33:32-33:88`.

The diagnostic extractor was also corrected to preserve already-instantiated
free-region identities across inputs and output, refreshing only erased
occurrences. Its optimized build exited 0 (32.66 s, RSS 523,336 KiB, swap 0).
Translation of the previously recorded, unproved ZST-specialized diagnostic
input still exits 2 at this live cast (0.43 s, RSS 92,752 KiB, swap 0).
This is diagnostic progress only; neither extractor preservation nor the ZST
transformation is asserted proved. Detailed candidate files and logs remain
under `.r21-scratch/r472-erased-only-regions/` and the isolated NUC candidate
`aspis-r472-erased-only-regions-candidate-20261003-a`.

Verifier source and security parameters were unchanged. No CU benchmark or
unchanged regression suite was rerun.
