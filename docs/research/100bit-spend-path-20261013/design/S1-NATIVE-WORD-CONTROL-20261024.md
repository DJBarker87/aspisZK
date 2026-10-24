# Original S1 claim: normal-return ordered control — 2026-10-24

**Checked:** the unchanged original Rust `prepared_claim` and the full-carrier
borrowed-ABI owned reference have equal complete Rust results and the same
ordered numeric child arguments, under common arbitrary normal-return child
tapes. All normal Rust rejection prefixes and the successful case are covered.
**Not established:** native numeric leaf interpretation/totality, abort/effect
transport, the final source-oracle prepare/model join, whole S1 or the actual
100-bit release claim.

No production Rust, frozen artifact or other owner's track was modified. The
controller evidence is not an adoption of the research numeric refactors.

## Exact checked cases

The compared native entry retains `&Verified<H>`, `&[u8]`, inactive WideExact,
`&[WideExact;29]` and kappa. Both sides use the complete actual native semantic,
field, accumulator and Error carriers. All semantic claims/extra/before values,
all eight words of each WideExact, input bytes and leaf results are arbitrary.
The source caller's expanded y1 frame is 928 bytes in this check. Hash is the
zero-sized test type; its digest panics if called. This is not a proof for an
unrelated stateful hash implementation or an oversized/short y1 slice.

A common tape describes powers, all 174 push poststates/errors, six finishes,
29 field reads and seven multiplications/additions. Every push checks its
complete 9-word private state, 8-word value and 4-word scalar. Every other child
checks its full input words and counters that establish its exact place in
the call order. Each returned Rust result is checked, including Parse rejection
and every word of the final value. Dot has no destructor; the reference's owned
Dot movement does not introduce a drop callback. Input references stay borrowed;
no public/semantic carrier is replaced by selected fields at the entry boundary.

Seven harnesses partition the first error: point 0 through 5, with arbitrary
column <29, and point 6 for no error. `S1FirstErrorPartitionV1.full_cover` proves
that these cover all ordinals ≤174; its index, counter and failed-field-count
facts fix the exact arithmetic. There is no independent source/reference
success premise or canonicality restriction in the seven normal-return checks.
The common numeric leaf contract is still explicit: this is not native TOTAL.

| First-error point | Exit | Wall seconds | Peak RSS KiB | Failed checks |
|---|---:|---:|---:|---:|
| 0 | 0 | 43.280 | 4,212,832 | 0 / 1640 |
| 1 | 0 | 53.850 | 4,532,844 | 0 / 1640 |
| 2 | 0 | 62.761 | 5,064,848 | 0 / 1640 |
| 3 | 0 | 73.471 | 5,338,156 | 0 / 1640 |
| 4 | 0 | 88.603 | 5,680,836 | 0 / 1640 |
| 5 | 0 | 84.783 | 5,790,548 | 0 / 1638 |
| 6: no error | 0 | 73.364 | 5,244,064 | 0 / 1638 |

Total 480.112 seconds, maximum 5,790,548 KiB RSS, zero swap. Each job ran
sequentially with fresh admission, optimized Rust flags, -j1, MemoryHigh=6G,
MemoryMax=8G and MemorySwapMax=0. Explicit outer-loop completeness bounds are
`min(point+2,7)` for BOTH source loops. CBMC's unwinding assertions remain
ENABLED and proved; no partial-loop assumption or unchecked truncated path is
used. The actual loop IDs are checked against retained GOTO inventories and
hash-pinned artifacts. Memory/time limits were not increased.

A negative native-step control flips the final word of the expected wide
argument without changing the actual source value. It fails specifically at
`eq8(words(value),VALUES[l])` (1 of 906 failed; 12.969 seconds, 1,233,200 KiB,
zero swap), demonstrating the word check is active. It is excluded from
accepted positive proof evidence.

## Why the previous checks timed out

A 20-second read-only GOTO diagnostic showed CBMC unwinding the harness's
bytewise `memcmp`, including 72 iterations for a 9-word state comparison,
before reaching the solver. Explicit eager comparisons of every 32/64-bit
word remove that artifact without reducing the compared bits. The unconstrained
full-rejection word harness still timed out (182.025 seconds, 6,487,304 KiB),
as did the first unpartitioned-point attempt (181.862 seconds, 6,517,792 KiB).
The verified finite point decomposition and checked completeness bounds removed
the irrelevant suffix expansion. No failed job was rerun unchanged with higher
resource limits. The older successful-child-only check (66.037 seconds) is
retained as ACCEPTED-ONLY history, not substituted for the seven cases above.

## Exact connection to the checked Lean reference

Kani uses shared borrowed private helper arguments. The earlier checked
reference source passed those private arrays by value. The new baseline
Aeneas extraction on the borrowed-helper source succeeded in 1.034 seconds,
101,376 KiB, zero swap, using the already pinned
`aeneas-b59d5188-lean432-extended-static` binary (not the experimental recovery
patch). The COMPLETE emitted function module equals the previously checked
borrowed-ABI reference module after removing only comments (even the remaining whitespace matches);
the emitted types are byte-identical. All five private/public reference Rust
functions are compared against the Kani input, not merely their output names.

Thus the existing `S1ClaimBorrowedAbiNativeV1`,
`S1ClaimBorrowedAbiTransportV1.borrowed_claim_eq_source`, owned inner/outer
inductions, original Prepared::new transport and enclosing caller proofs can
be reused without rebuilding unchanged targets. Generated external templates
remain raw/unimported; no custom axiom or opaque native evaluator is installed.
This does not discharge their concrete numeric/Std/P6 source interpretation.

## Source freeze and remaining trust boundary

`s1-native-word-control-source-pins.json` checks verifier.rs AND candidate.rs
separately across b2727acd3…, 25866ec331… and b797d6d360…. Those complete
controller/caller files are equal. The relevant field/powers and outer Dot
method spans are separately pinned. Whole weights.rs and fast_pairing.rs differ
across revisions; r1_wire.rs differs in the older b272 history but is equal
between 258 and b797. Matching controller or outer-method text does not certify
changed transitive numeric helpers, nor attach a historical proof to them.

The Kani native crate/dependencies, Cargo.lock, tools, flags and before/after
source inventories are exact in each receipt. Historical host receipt revision
d8fc9db… is not the submitted kit identity; the source hashes and frozen-body
comparisons identify it. Source-only packets distribute no GOTO/LLVM/LLBC,
executables or compiled Lean objects.

Actual correspondence with the concrete Lean arithmetic installation still
requires the powers/field/c0/newDot/pushDot/finishDot interpretations and the
hardcoded wide add/mul and release trace behavior. The controller certificate
supplies common NORMAL-return argument/order/result equivalence. Extending it
to native aborts/divergence, actual numeric purity/effects and the exact frozen
leaf implementations is a separate gate, not an invented per-call axiom.
The source Program's prepare/op7 ordered-read/state join and its identification
with frozen2 remain open; a pure value theorem is insufficient for that join.

`S1FirstErrorByteRangesV1` additionally proves the exact source field expressions
`column*32` and `(column+1)*32` fit the 928-byte frame and that all controller
indices fit even a 16-bit usize. These are TOTAL arithmetic bounds on the stated
source loop domain. They do not prove `from_le_bytes(...).unwrap()` total for
arbitrary noncanonical byte strings. The two arithmetic targets passed in
12.225109917 seconds total, peak 830,947,328 bytes, zero swap and seven standard
axiom reports.

No source adoption is needed for this controller proof. Using changed research
numeric leaves as the frozen release implementation still requires the relevant
owners' equivalence, source/artifact and affected-parent re-pin gates. No such
adoption or whole-cone closure is asserted here.

Audit:

```
python3 tools/s1-claim-word-checks-20261024/check.py
```

Packets: `evidence/s126-current-caller-20261021/s1-native-word-control-20261024`
and `s1-native-borrowed-helper-20261024`, plus exact arithmetic receipts and
`s1-first-error-partition-import-pins.json`. The next enclosing deliverable is
the concrete native leaf/abort interpretation and prepare/op7 source-oracle
state/ordered-read join, using the already checked caller/challenge trace.
