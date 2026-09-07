# Grouped binary masks no longer require a dense chord transpose

Research base: fe506bfcdf4d8b4604e2fa0cfe3ea9c577d54021. Date: 2026-09-07.
Only research artifacts changed; production and concurrent worktrees untouched.

## Result

The selected inactive-mask family now has a concrete fast reference for chord
transport followed by all four actual dual folds. It uses **142 generic QM31
products plus 170 mixed M31 products**, including challenge-power preparation,
and returns all four terminal values. It does not materialize a 1024-entry
transformed covector. There is a 64-row contraction, with values accumulated
directly into four outputs.

2080 binary-mask tests passed (every one of the 1024 weight basis vectors under
two challenge tuples, plus 32 further masks). The three compiled source profiles
also passed, as did 20 aggregate cases containing three MLE covectors, two
circle-OOD covectors, the selected forest mask and both image constraints.
These are exact arithmetic tests, not a transcript, privacy or CU certificate.

## Source alignment

`programs/aspis-verifier/src/v7_verifier.rs` passes the frozen pair-forest row
groups and group masks into the selected prepared transcript/relation verifier.
`pair_forest_copy_terminal_constants.rs` has seven distinct inactive masks;
the earlier private-transfer/withdrawal profiles have eight each. The prototype
reads the exact active arrays and complements their u16 values, matching
`pool_inactive_row_masks` and the selected source's tested prepared representation.
It does not invent a representative mask with a favorable pattern.

Pinned file SHA256:

- pair-forest constants: cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50
- earlier payment constants: 8e042b07ed259f8b408d097453dff1a9f946b0e21423e0f746f84806bd3898d7

The prototype rededuplicates the 64 masks for convenience. A future verifier
adapter should consume the already-validated frozen row groups; no CU saving
from removing that setup has been measured or included here.

## Why the construction works

Split the coefficient index into a four-bit low digit and six-bit high row.
For each low input digit, apply the chord a+bx+cy through the exact carry rules:

- a preserves its digit;
- b*x follows the multiplication-by-x carry paths;
- c*y sends A to yA and sends yB to (1-T2)B/2.

A carry leaving the low digit is an active Chebyshev carry into the high row,
**not an integer increment of that row**. The prototype retains separate
normal and active-carry arrays over the 16 low output positions. It contracts
each distinct binary mask against both arrays using additions only. For high
input row j, take the normal value for that row's mask and add the active values
on each terminating high carry path, with its exact power-of-two coefficient.
Weight those 64 results by the last two dual blocks and accumulate by the two
unfolded top bits. Deferred normalization divides the four outputs by 256.

The active x carry can leave only low positions 0/1, and the active y carry
only positions 0/2. These structural zeros reduce low chord combination from
80 to 52 generic products. They are asserted in the optimized test build.
Counts are 26 products for two 16-entry dual bases, 52 for low chord combination,
and 64 for high accumulation: 142 total. Mixed products are 30 low x paths,
14 low y paths, and 126 non-overflowing high paths: 170 total. Additions,
halvings, indexing, deduplication and allocation are separate costs.

The first unoptimized sparse version took 170 generic products. The subsequent
run changed the implementation to exploit proven carry sparsity; it was not an
unchanged regression. Later runs added the aggregate/source-order tests.

## Aggregate relation and source order

The aggregate control materializes the original weights independently using
big-endian MLE coordinates, and evaluates circle basis values directly.
The fast path reverses MLE coordinates into the low-bit product convention,
uses the two-bit Product kernel for the three MLE and two OOD components, and
uses the new grouped kernel for the inactive mask. It then adds the dual folds
of the two sparse image claims. Every one of the four terminal values agrees
with dense transpose followed by the literal source dual-fold order.

Both original circle-OOD covectors are retained as a conservative control.
Their removal from a proposed V8 transcript would require an explicit argument
that reconstruction plus image membership already enforces those evaluations.
This test does not assume that optimization or change acceptance.

All three image-weight coefficients are at indices 1021–1023, so after four
dual folds they affect only terminal index 3. For coefficients
`(-eta²*c, eta²*b, eta)` respectively, the added terminal value is

    [eta*alpha0 + eta²*(b*alpha0²-c*alpha0³)]
      * alpha1*alpha2*alpha3 / 256.

This is a deterministic coefficient identity. It is not a claim that eta may
be introduced at any transcript point with an uncharged two-root error.

The tested assembly gives a conservative generic-product budget of
5*91 + 142 + 10 + 1 = 608, counting outer scales, separately recomputed challenge
powers, the sparse-image expression and kappa². Input point/factor generation,
mixed arithmetic and all non-weight verifier work are excluded. This is not
an instruction count, minimal implementation, or comparison against selected V7.

## Commands and observed measurements

From the research worktree root:

```sh
rustc --edition=2021 -O -C debug-assertions=yes docs/research/v8-no-work-100-20260907/experiments/chord_link.rs -o /tmp/aspis-v8-grouped-check
/usr/bin/time -l /tmp/aspis-v8-grouped-check --grouped-test
```

Final changed-source run: exit 0; 0.63 s wall; 0.23 s user; maximum RSS
2260992 bytes; zero swaps and block input/output operations. Rust 1.93.0,
Apple M3, Darwin 25.5.0 arm64. Compilation excluded from the timed execution.
This is optimized arithmetic with structural assertions enabled, not debug mode.

Warm host timings, 200 calls each, including rededuplication and allocations:

| Source profile | Mean | p50 | p95 | Maximum |
|---|---:|---:|---:|---:|
| Selected pair-forest | 5235 ns | 4791 ns | 7375 ns | 25459 ns |
| Earlier transfer | 4882 ns | 4875 ns | 4958 ns | 6917 ns |
| Earlier withdrawal | 5060 ns | 4958 ns | 5125 ns | 10542 ns |

The tail is reported rather than replacing it with a favorable earlier run.
No full proving time, SBF stack size, transaction CU or peak full-prover RAM
is inferred from these measurements.

## What is and is not settled

The product and selected grouped-binary families now both have exact efficient
constructions. Dense expansion is not intrinsically necessary for the tested
pre-query covector transformation. Arbitrary Dense field-valued components,
accepted-wire translation, intermediate sumcheck polynomial construction,
interpolant claim correction in that transcript, query-rho terms, malicious-input
handling and full-view hiding are not established by terminal equality alone.

The parallel V8 branch advanced to 1e1f17529ff1aa1c07b68b6f28c41a994abd77fb.
It now has committed partial-provider/hiding-criterion work and uncommitted
scalar-fingerprint and Linux/SBF evidence. The draft 2800-root family bound
concerns nonmatching fingerprints of already available candidate tuples; it
does not itself bound K1.4-classifier failures mapped to `none`. Its newer
conditional ledger therefore must not be substituted for a completed recovery
argument. Reported partial V7 CU runs and V8 stack-frame failures were not run
here and are not a matched four-shape V8 comparison. All concurrent work was
left intact; no remote jobs were launched.

The next engineering gate can use these kernels rather than the dense reference.
The next **security** gate is still a joint recovery/support-loss argument that
survives the explicit boundary counterexamples. No 100-bit/CU-parity claim is
upgraded by the successful arithmetic.
