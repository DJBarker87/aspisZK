# Prover commitment part 26

Base `57ca9c452`; branch `codex/cx-prover-commit26-20261021`.

Target not yet established. This report is updated after each verified stage.
No shipped file or concurrent-owned module is changed.
The last, job-specific attempt assignment 7584–7699 takes precedence over
the earlier overlapping ranges; check the shared receipts before each use.

## Stage 1 — split arithmetic gates

Pending: verify the exact paired division cell, then its verified-stub limb
caller, then Lean induction over limb/digit schedules. The 600/180-second
predecessor gates remain excluded; neither is rerun unchanged.

The exact arithmetic-cell contract passes (`cell-v1`): all `u64` remainder
and `u32` limb inputs satisfying pairwise equality, using the two literal
shift/or/division/modulo expressions, return equal quotients and remainders.
Exit 0, wall 30.733 s, peak RSS 132804 KiB, swap 0. `limbs-v2` uses
`stub_verified(paired_cell)` for the reverse-iterator/decrementing-index
product, retaining all eight output limbs: exit 0, 0.899 s, 148056 KiB,
swap 0. `limbs-v1` is an excluded missing-stubbing-feature compiler error.
All Rust gates use the requested 6G/8G/no-swap/64-task cap and RUSTFLAGS.

`ProverCommitLowDigits26.limbs` proves the symbolic loop invariant for the
iterator fold, including an arbitrary previously written quotient prefix.
`pass` identifies the whole fold with the existing machine-process model;
`digits` proves all remainders and the entire retained quotient equal for
any number of digit passes. `low_digits`, `remaining`, and `canonical`
transport the existing arithmetic meaning. J7585: exit 0, wall 0.87 s,
peak RSS 1711236 KiB, swap 0; all six axioms audits use only the standard
three axioms or fewer. J7584 is an excluded reserved-identifier parse error.
Exact sources, revisions and dependency fingerprints are in `lean/`.

Two array-valued contract experiments (`pass-v1`, `pass-v2`) were stopped
near 6.1 GiB process RSS before increasing pressure. They are excluded;
the second changes the independent-input precondition into a shared input.
Neither improves the successful small limb harness. These diagnostics are
retained with source snapshots and resource receipts. No cap was raised.
The useful replacement is the small verified-cell product plus symbolic
induction; no full arithmetic network is replayed.

Scope: the new Lean induction is a machine/list-model theorem. Source
binding still relies on the separately checked control skeleton and P6;
it is not a new Aeneas theorem identifying the original iterator body with
the extracted indexed body. This distinction must remain visible at the
whole-source boundary. No endpoint premise is removed at this stage.
