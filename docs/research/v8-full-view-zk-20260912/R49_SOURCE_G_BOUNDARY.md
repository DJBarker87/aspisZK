# R49: source G boundary and fixed residual matrix

Base `510b95490b59fdb8b6887187e88400299f3687ed` (R48).
Branch `research/v8-r49-source-g-boundary-20260929`.

## Result

**36 new Lean theorems compile with standard axioms only.** The ordered G
scatter, final constant-coin write and three statement-point constructions
are connected to the full-support R48 functionals. The ordinary/G weights
at the retained algebraic witness now equal R43's certified formulas,
including the G boundary term. The source-shaped residual matrix over
**exact QM31**, for every distinct 22-root tuple, equals the embedded
certified matrix and has nonzero determinant.

This is a fixed-specialization exact-field theorem, not an assertion that
the specialization is an accepted source prefix, a probability bound, a
Rust word/kernel extraction or global privacy. No verifier or protocol
change, no new Rust/SBF execution. Retained CU is **1,620,236 / 1,621,719**;
both 1M-cap runs still exhaust.

## What the source composition proves

The source scatters coefficient `coins[i]` to original row
`order[128+3*i]`, in ascending `i`. A generic fold-of-updates proof shows
that this ordered assignment has exactly those values, and is zero outside
the selected rows. The T163 permutation is injective and none of these
rows is the balancing pivot.

Within code coordinates 0 through 130, the only selected coordinate is
128. Therefore the complete low quotient functional is exactly

```
coins[0] * chordEntry(half, a, b, c, r, 128),  r < 128.
```

This is proved for arbitrary values of all **270 other coefficients**.
Their formulas need not be unfolded to establish this restriction, and
they are not assumed zero or resampled. The source executes ten scale
multiplications in reverse round order and finally writes coin 0. The
generic scale-loop theorem proves that write is `half^10`, regardless of
all earlier coefficient writes. Thus the precise G boundary survives.

The statement-point proof follows `v6_statement_points`: initialize the
last successor coordinate as `1-z[9]`, initialize carry with `z[9]`, then
update coordinates 8 down to 0. Its exact-field result is the retained
suffix-product formula. The sequential XOR updates at 7 and 6 give the
third point. No Boolean restriction on field challenges is assumed.

Original weight construction adds the point tensors, the inactive
indicator and, in the G channel, the scattered functional. The inactive
indicator cancels under the exact T163 dual subtraction. After the chord
transpose, the fixed weights are

```
wr = 5*e0 + 25*e1 + 125*e2
wg = 25*e1 + 125*e2 + 5*hg
hg(r) = half^10 * chordEntry(half, 7, 5, -5, r, 128).
```

Both channels retain their image updates and arbitrary image challenge.
R48's support theorem justifies restricting these correction equations
to 32 whole blocks. The point rows and all seven coefficients in each
channel then match `HighWitnessTransport.observed` exactly, not merely at
random examples. The complete row model has three point rows and fourteen
coefficient rows; the retained certificate selects thirteen of them.

Ring-homomorphism lemmas lift the **full 131-coordinate** point functional
and these weights. Over exact QM31, the same source-normalized columns
therefore give the embedded R43 matrix for every injective 22-root tuple.
The determinant theorem reuses the retained inverse certificate, not a
fresh determinant expansion or a new field axiom.

The fixed values remain `z=[0,0,0,1,1,0,0,1,0,2]`, kappa 5, alpha 7 and
normalized chord `(7,5,-5)`. They are an algebraic nonvanishing witness,
not an accepted OOD transcript or the actual challenge distribution.

| Leaf | New theorems |
|---|---:|
| `SparseGScatter` | 7 |
| `SourceGConstant` | 4 |
| `OriginalChannelWeights` | 3 |
| `SourceStatementPoints` | 4 |
| `SourceFixedResidual` | 6 |
| `FullWeightHom` | 4 |
| `SourceFieldResidual` | 8 |

## Source pins and execution

The gate directly checks the retained R43 stage hashes of
`r18_sparse_coded_g.rs`, `r17_structured_g.rs`, `r17_opening_weights.rs` and
the current `crates/aspis-core/src/v6_transcript.rs`. The latter is unchanged
at SHA256 `48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf`.
R48's complete pin manifest also remains unchanged.

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r49_evidence.py
```

Result: **24 artifacts**, **258 pins**, **250** cached objects checked.
Seven successful new leaves: **10.73 s** combined wall time, maximum RSS
**2,479,948 KiB**, exit 0 and swap 0 throughout. All 36 axiom audits contain
only `propext`, `Classical.choice`, `Quot.sound`.

Serial cached Lean 4.32.0 scopes on the NUC used `MemoryHigh=3G`,
`MemoryMax=5G`, `MemorySwapMax=0`, `TasksMax=128`. Five failed plumbing
attempts are retained, including a missing retained field instance; no
resource/recursion limit was raised. The finite statement-point proof has
only ten symbolic factors, not a large recurrence or field enumeration.
Exact target, command, base/source revision, wall time, RSS and axiom output
are recorded per target. Unchanged Rust/CU suites were not rerun.

## First remaining proposition

Construct the **new fixed-query challenge polynomial** from these complete
source-shaped functionals: fix an arbitrary distinct root tuple, vary the
semantic/point, kappa, alpha and normalized chord challenges, and identify
evaluation with the source-normalized correction matrix. Prove its own
degree and nonvanishing using this exact-QM31 specialization. Include the
G boundary and justify transfer from normalized to actual rational chord
coordinates. The old 1,105 degree bound is not inherited automatically.

Then justify the actual shared-oracle conditional law with the real
chronology, bounded samplers and adaptive query/publication behavior. A
nonzero algebraic witness does not discharge that law. Preserve the
posterior target `b - B A^-1 a` and both pre-beta channel observations.

Further open requirements include Rust canonical-word/array and optimized
kernel refinement (including compact versus reference computation), source
sampler premises, full joint semantic/H1 coverage, coherent pre-beta
extraction for soundness, seed/commitment assumptions and visible
failure/retry/publication accounting. The new source-shaped loop equalities
do not assert a complete extraction of compiled Rust. C1 negative
regressions remain; no new hiding assumption was introduced. Full privacy,
soundness closure and supported-budget execution remain unfinished.
