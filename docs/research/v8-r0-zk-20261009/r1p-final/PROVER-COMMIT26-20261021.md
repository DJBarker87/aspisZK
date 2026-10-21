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

## Stage 2 — concrete query callback and extracted continuation

`ProverCommitQuery26.policy` installs the concrete query callback along with
all three scalar policies from part 25; no query callback parameter remains.
It uses the retained concrete LE/mask decoder, list scanner and first-stop
driver, starting at the explicit zero scanner. `success` supplies both the
selected-state driver trace and the full concrete Q22-valid per-block chain.
`rejection` maps scan failure to Transcript. `caller` factors the *actual
extracted* eager sixteen-read schedule from this concrete callback and the
literal 22-entry trace continuation; it retains all failure/divergence cases.
`finish_rejection` proves that query failure retains the absorbed state and
previous trace. These are owned-source/model facts, not a shipped FS experiment.

J7615 passes all six top-level audits: exit 0, wall 4.35 s, peak RSS
4030576 KiB, swap 0; only [propext, Classical.choice, Quot.sound].
The source factorization is checked byte-for-byte by `harness/check-query26.py`.
The proof uses shallow bind congruence with explicit tuple normalization;
it does not raise depth/heartbeat options. J7601–7614 retain all failed
elaboration/normalization diagnostics and exact snapshots.

Thirteen retained query owners are now compiled from pinned source into Env J,
coherently with the installed scalar/source closure. J7586–7589, J7592–7600
pass. J7590 is an excluded monadic elaboration port failure; J7591 is a
preflight-only missing dependency. The driver proof port replaces inferred
pair-bind elimination with explicit bind elimination; no statement or
executable body changes. `query-owners.json` and `query-ports/` pin every port.

Source/library gates: `query-iterator-v1` proves all eight actual IntoIter
values and exact exhaustion (0.598 s, 145840 KiB); `query-decoder-v1` proves
source from_fn/map versus ordered LE/mask parsing (0.789 s, 168940 KiB);
`query-driver-v1` proves outer loop versus first-stop unrolling, including
all observed block bytes and selected advance bytes, for arbitrary stop
responses (6.572 s, 389884 KiB). Every gate exits 0 with zero swap.
The driver's scan callback is abstract: this is a control theorem, not an
assertion that the complete native scanner equals its model.

The direct complete eight-word scanner comparison timed out at 90 s;
its variable-prefix membership diagnostic timed out at 60 s. Neither counts
as verification. Replacing the symbolic slice length by *every* fixed length
0 through 22 yields 23 successful source-contains/explicit-membership gates:
1.18–1.65 s each, under 267000 KiB, zero swap, with unwinding assertions.
The complete old scanner gate is not rerun. These fine-grained gates close
library/control obligations; their full source-to-Q22 composition still needs
an exact scanner execution transport theorem. The standard trust list is not
expanded to include that desired conclusion.

### Unconditional query reference totality

`ProverCommitQueryTotal26` removes the successful-call premise at each
construction layer: generic stateful from_fn totality, concrete byte-rank
and masked-word totality, valid scanner transition totality, first-stop
finish totality, the complete eight-block driver, and finally the installed
query callback. All input bytes remain universally quantified. Query rejection
is retained as a normal result, not assumed away. This closes the totality
of the concrete policy, while source correspondence remains a separate claim.

J7621: exit 0, wall 2.49 s, peak RSS 3987544 KiB, swap 0; all nine audits
standard-only. J7618 and J7620 are focused predecessors (2.01/2.45 s,
3974852/3981816 KiB, zero swap). J7616/7617/7619 are excluded elaboration
failures. Source snapshots, dependencies, errors and complete audit lines
are retained in the per-attempt evidence. No new depth/heartbeat limits.
