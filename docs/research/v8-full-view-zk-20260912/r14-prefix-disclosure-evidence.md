# R14 prefix/disclosure boundary

Date: 2026-09-14.  Branch: `research/v8-privacy-repair-20260913`.
Packet source pin and starting HEAD: `6eb14741b87b9edef4b046759296e80563f7d20d`.

## Locked inputs and executable checks

- `python3 scripts/check_manifest.py`: exit 0, 66/66.
- `python3 scripts/check_source_pins.py /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913 --check-working-tree`:
  exit 0; all selected 12 pins match, including the packet HEAD.  It does not
  assert a generated q22 closure.
- `python3 verify.py`: exit 0; 46 tests passed in 24.960 s.
- `bash scripts/run_cpp.sh`: not runnable on this macOS cache: the installed
  compiler cannot locate `boost/multiprecision/cpp_int.hpp`.  No package,
  toolchain, or source change was made to work around that environment gap.

## Lean leaves

The six supplied R14 leaves and aggregate import were compiled unchanged in
the cached `AspisFormal` workspace with `lake env lean -M1800`, one target
at a time.  All exited 0; swap was 0.  Peak RSS / wall time were:

| target | wall | peak RSS |
| --- | ---: | ---: |
| `TwoCommitments` | 4.70 s | 669,597,696 B |
| `PublicPrefix` | 1.00 s | 669,663,232 B |
| `FinalRoundObstruction` | 6.34 s | 1,346,142,208 B |
| `FiberContinuation` | 2.17 s | 1,305,477,120 B |
| `DisclosureBoundary` | 2.06 s | 1,404,649,472 B |
| `ReadVisibility` | 1.03 s | 669,597,696 B |
| `AspisV8R14` aggregate | 0.77 s | 669,466,624 B |

`TwoCommitments`, `PublicPrefix`, `FiberContinuation`, and
`DisclosureBoundary` report only `propext`, `Classical.choice`, and
`Quot.sound` where applicable; `FinalRoundObstruction` reports
`propext`; `ReadVisibility` has no reported axioms.  These establish the
ideal finite-model commitment/prefix normalization, restricted final-round
obstruction, compatible-fibre continuation, and disclosure accounting.  They
do not assert literal prover equality, an actual Fiat--Shamir law, or full
privacy.

## Actual-source tests

All Rust commands used `--offline --release` and `CARGO_BUILD_JOBS=1`.
The four R14 Rust sources are individually `rustfmt --check` clean.  A
workspace-wide formatter check still reports pre-existing unrelated formatting
drift, which was left untouched.

- `r14_public_prefix`: exit 0; literal initial eta and three compact rounds
  match the pinned Python fixture.
- `r14_final_obstruction`: exit 0; G plus mask-only lanes leave the three
  high invariants.
- `circle_candidate::r14_raw_disclosure::r14_q4_q6_separator_lifts_to_twenty_two_queries`:
  exit 0; the actual C1 encoder's q4/q6 functional remains
  `490597912` at row 913 and remains a separator after zero-extension to a
  22-query schedule.  It is a test-only child module of `circle_candidate`
  because the encoder basis method is intentionally `pub(crate)`; no
  production visibility or protocol path was changed.
- `r10_semantic_cut r14_source_offsets_`: exit 0; the actual eta-after-initial
  callback and three actual round challenges preserve G-offset affinity.
- Retained source regressions were rerun: the same-public valid
  duplicate-input witness and the 768 raw C1 pair-family gate both exit 0.

## What the negative result means

The q4/q6 certificate is a literal source-valid raw C1 separator, not a
full-transcript privacy theorem or an advantage bound.  Conditional on an
ideal uniform 22-subset sampler, a fixed pair appears with probability
`11 / 1,636,171,776` (about `6.723e-9`); the declared union over 128 groups
is about `5.163e-6`.  Neither number is a source-valid probability or a
privacy lower bound yet: the actual sampler, duplicate/draw-cap/stopping law,
publication event, and relation to the full source transcript are not proved.

The first remaining source proposition is therefore the actual q22
query/stopping/release law, including its coupling to the retained
same-public duplicate-input witness.  Separately, any positive simulator
route still needs the actual R12 inverse/public simulator construction for
arbitrary targets under the real callback chronology.  The local G-offset
test is not that construction.

The subsequent R15 source-slice audit narrows the syntax-level part of this
boundary to a direct 22-query/64-draw callback and now recovers its exact
pinned v4 performance companion from the retained generator and a
hash-authenticated one-line delta. See `r15-q22-source-slice-audit.md` and
`r15-q22-stopping-evidence.md`; this does not close the q22
query/stopping/release proposition.

No production protocol path, negative regression, hiding assumption, merge,
deployment, wallet operation, or push was performed.
