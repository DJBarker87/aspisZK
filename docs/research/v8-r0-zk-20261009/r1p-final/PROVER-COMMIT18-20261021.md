# Prover commitment part 18 — shipped experiment audit

Base `c35b7b481`; branch `codex/cx-prover-commit18-20261021`.

## Target and boundaries

Construct the actual shipped experiment, prove both fixed-event whole-run
joins and specialize the deployed endpoint. Concurrent-worker modules
SourceIdentification, RustRuntimeJoin and PrivacyR1FinalRelease are untouched.
No production source or security contract is changed.

## Stage 1 — entropy and retained state

The source entry point calls `StateOnlyAttemptSecrets::generate`, which
performs up to sixteen 96-byte OS draws. Each draw contains three 32-byte
blocks; a zero block rejects the whole draw. OS error aborts immediately;
sixteen rejected draws return `RepeatedZeroBlock`. Neither error is a
`MaskSampleExhausted` retry. `prove_masked_retrying_with` maps entropy failure
to `Error::Entropy` and aborts rather than using another of its eight attempts.

`ProverCommitEntropy18` defines this control-flow adapter with explicit OS
error and retained draw state. Its successful result is the existing `SecP`
carrier. The all-zero and OS-failure paths remain errors. No OS law, source
translation or full FS-experiment claim follows merely from this definition.

Validation and remaining stages are recorded incrementally below.

J8656 exposed two syntax/type-annotation errors and is excluded. Changed-source
J8657 passes all seven audits: exit 0, wall 2.35s, peak RSS 3,498,544 KiB,
swaps 0; revision `c35b7b481` plus the exact source hash in `lean/`.
`no_total_success_adapter` has no axioms; the other six use only
`[propext, Classical.choice, Quot.sound]`. This is a model/control-flow result,
not an impossibility theorem for the shipped privacy experiment. It forbids
silently replacing every entropy outcome with a successful nonzero secret.
The host used the slot launcher with 6G/8G/no-swap/64-task caps. No existing
shared source/object was overwritten and no dependent replay was needed.

## Stage 2 — necessary failure transport

`ProverCommitEntropyJoin18.failure_mass_le_bad` proves a necessary condition
for a coupling which agrees outside a fixed event: any observable runtime
failure absent from the model must have mass no greater than that event.
The concrete finite `RawRand = Fin 16 → (Fin 3 → OracleAnswer)` represents
sixteen independent uniform 96-byte draws, with no OS errors. It is not a
claim that the OS actually has this law. The zero draw trace has positive
mass; thus `no_exact_success_coupling` rules out an *unconditional exact*
coupling from this sampler to an always-successful `SecP` sampler.

This does **not** rule out the requested whole-run coupling outside
`realBad`/`selectedBad`; their budgets may cover a failure transport. It also
does not establish any lower bound relevant to the privacy target. In
particular positive mass is not compared with the existing query-scan bound.
The missing entropy component must account for this branch rather than
claiming an error-free type conversion.

J8658 failed on a missing namespace opening. Changed-source J8659 passes all
five audits with standard axioms: exit 0, wall 1.89s, peak RSS 3,521,096 KiB,
swaps 0; revision `6352cfd55` plus exact source hash. Fixed launcher caps
unchanged. The dependency was the accepted J8657 object; no old shared object
was overwritten. All failure receipts are excluded from accepted evidence.

## Stage 3 — exact successful-draw symmetry

`ProverCommitEntropySymmetry18` constructs a bijection of raw 96-byte
candidates for *any* permutation of `SecP`: valid candidates are permuted and
invalid candidates stay fixed. `run_equivariant` transports the entire
bounded draw loop with the same draw-state history, cursor and OS failures.
`successful_law_equal` proves that every two successful secrets have exactly
the same mass under sixteen independent uniform raw draws. The failure
outcome remains present in the unconditioned law. No giant carrier is
enumerated. This supplies the mathematical symmetry needed for a conditional
success law; it does not supply an OS law or erase the failure probability.

J8660 failed on local rewrite normal forms and an unqualified helper;
changed-source J8661 passes all seven audits using only standard axioms:
exit 0, wall 2.64s, peak RSS 3,501,884 KiB, swaps 0, revision `0549f01af`
plus exact source hash. Two harmless no-op `change` lints remain in the
inverse proofs. Source dependencies J8657/J8659 are unchanged and reused.
Caps remain 6G/8G/no-swap/64 tasks; no old shared module is overwritten.
