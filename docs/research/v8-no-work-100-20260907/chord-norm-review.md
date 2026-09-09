# Share the chord norm across its four sign variants

Research continuation of `e45296c7877d787965c908ab153b08d960411c3d`,
2026-09-09. Retain the six-coefficient norm control **on top of** the measured
descriptor-sort winner. This is a new shared-computation optimisation, not
the previously rejected generic QM31 batch inversion or four-channel gamma
fusion. Main, production, wire, transcript and all repaired checks stay unchanged.

## Complete transaction decision

| Shape | Descriptor-sort maximum | Shared-norm maximum |
|---|---:|---:|
| Transfer, current page | 1,065,839 | **1,063,909** |
| Transfer, rollover | 1,078,664 | **1,076,729** |
| Withdrawal, current page | 1,084,123 | **1,082,205** |
| Withdrawal, rollover | 1,097,085 | **1,095,156** |

The same maximum-body proofs save another **1,905–1,998 CU** each. All24
maximum-body cases,24 ordinary-body cases and two post-real-verifier
Token-CPI-failure rollback controls pass with matching outcomes, protected
accounts and atomic settlement. Proofs, Pool, Registry, Token3.5 SBF and runtime
are unchanged. Unsupported rollover stale/replay cases are not counted.

The measured worst has **104,844 CU headroom** below the actual1.2M TxV1 cap.
Body maximum remains **40,282 bytes**. Both new controls together reduced the
previous1,100,125-CU maximum by4,969 CU. This is a measured combined build,
not addition of independently optimistic stage estimates. Same-pool selected
V7 remains cheaper by **23,086 /42,328 /45,840 /46,272 CU** respectively;
these are fixture maxima, not universal CU coverage or V7 parity.
See [machine-readable results](chord-norm-results.json).

Selected ELF is **1,007,728 bytes**,5,536 bytes larger than the descriptor-sort
ELF, SHA256 `805e668f19823e335a4419ada76d2249c10a95a39a334bca9544a8a7dd65ec27`.
This executable-size cost is not proof-body growth.

## Exact shared expression

Write a QM31 value as `v0 + u*v1`, with `u²=r=2+i` over CM31. Its first tower
norm is `N(v)=v0²-r*v1²`. Define the polar expression
`B(v,w)=2*(v0*w0-r*v1*w1)`. For a public chord `a+b*x+c*y`, precompute
six CM31 coefficients:

```text
N(a), N(b), N(c), B(a,b), B(a,c), B(b,c).
E = N(a) + N(b)*x² + N(c)*y²
X = B(a,b)*x; Y = B(a,c)*y; Z = B(b,c)*x*y
norms in source slot order (++,+-,--,-+):
  E+X+Y+Z, E+X-Y-Z, E-X-Y+Z, E-X+Y-Z.
```

The implementation uses two butterfly pairs to share the additions. The
initial proposal had five coefficients after eliminating `y²` using the circle
equation. This first measured control deliberately retains six: its identity
holds for **arbitrary base-field x/y**, with no new circle-membership premise.
The circle-only simplification is separately Lean-proved but not enabled.

[ChordNorm.lean](experiments/ChordNorm.lean) proves the polarized identity and
all four source-ordered norm outputs over any commutative coefficient ring.
It also checks the coordinate expression for multiplication by `2+i` and
the conditional circle simplification. The first two theorems supply the real
saving: every recomputed norm is the same CM31 value as the previous direct
norm, including zeros. No division or probability estimate enters that rewrite.

The actual callback constructs the denominator Vec from **the same** `p.abc`
and original query points passed to the private helper. It checks zero point
coordinates as before; the helper retains empty/zero-denominator rejection.
The second norm, M31 batch inversion (including zero-norm rejection), conjugate
scaling and reconstruction of each QM31 inverse are literal copies of the old
downstream computation. No root/opening, gamma value, query order, numerator,
fold, rho injection or relation response is changed. The helper's extra length
guards are outside the already fixed private caller contract, not a new public
hint format. A mismatched externally supplied denominator/point tuple is not
claimed equivalent; the verifier constructs it, not the prover.

Rust controls compare every intermediate CM31 norm and every final inverse to
the old tower path, and check `value*inverse=1`. They cover1,024 arbitrary
22-point/chord profiles, including off-circle points, all-zero/maximal limbs,
single nonzero field coordinates, explicit zero denominators and legal zero
coordinates of nonzero values;16 further profiles use the actual selected
log20 domain routine. Shape and empty-input failures remain visible. These
are deterministic tests, not a security probability measurement.

The Lean theorem is a universal algebraic model. The actual CM31/QM31
representation, canonical field kernels, callback argument/index construction,
Vec iteration and compiler remain source-audited/tested rather than newly
translated into Lean. Existing range-proved field overlays are unchanged
(field source SHA256 `bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0`).
No dishonest-proof premise is used to erase a residual or skip a check.

## Costs, including preparation

For the changed first-norm computation only, the old path performs176 CM31
squares. The new path prepares6 CM31 squares and6 CM31 products once, then
performs110 CM31/base scalings and66 base products for x²,y²,xy over22 fibres.
With the retained two-product CM31 square and four-product selected CM31
schoolbook multiplication, that is **352 versus322 base products**: only30
products saved after setup, not an eightfold speedup. Addition, reduction,
indexing and compiler effects also change; the measured CU difference is not
attributed solely to those30 products. The remaining inversion/fold work is
not included in this limited operation model because it is unchanged.

Six coefficients occupy48 bytes of payload. The norm Vec still represents
88 CM31 values/704 bytes, and the inverse output length is unchanged. The
allocator/whole-frame peak delta was not separately measured; no zero is
invented for it. There is no new prover buffer or public message, and no
prover-time/RSS/search rerun. The body census remains
`697*16+52+24+22*621+2*296*26 = 40,282`.

## Resources and reproducibility

| Focused target | Exit | Wall seconds | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Optimized source test/build | 0 | 33.89 | 560,288 KiB | 0 |
| Complete SBF build | 0 | 33.84 | 591,648 KiB | 0 |
| ChordNorm Lean leaf | 0 | 4.64 | 2,895,609,856 bytes | 0 |

All four Lean declarations pass on their first focused replay, with only
`propext`/`Quot.sound` and no `sorry` or new axiom. Lean4.32.0/Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` and Tactic cache provenance are
recorded in the log. No unchanged proof suite was replayed. NUC compilation
dominates the Rust jobs; build scopes High5/Max7 GiB/jobs2, SVM High3/Max4 GiB,
all SwapMax0. The same pinned Rust/SBF/LiteSVM/runtime setup as
[auth-order-review](auth-order-review.md) is used. Executed ELF direct-r10
offsets are≤4,096 with no new stack warning; not a whole-machine stack proof.

`audit_chord_norm.py` reconstructs the measured callback from a literal patch
against the full starting revision; it verifies source/proof/program hashes,
all matrix outcomes, resources and axioms. The previous auditor/results still
reproduce unchanged. Only synthetic public JSON/log evidence is retained.

```sh
bash experiments/run_chord_norm_lean.sh NEW_ABSOLUTE_LOG
# Pinned task-owned NUC copy with existing overlays:
bash experiments/run_chord_norm_nuc.sh NEW_TEST_LOG
bash experiments/run_complete_build_nuc.sh chord-norm NEW_BUILD_LOG
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh chord-norm NEW_MAX_DIRECTORY
ASPIS_V8_CHORD_NORM=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
python3 experiments/audit_chord_norm.py
```

Remove only the max-fixture variable for ordinary proofs. `experiments/`
abbreviates this research directory. Keep the1.4M driver CLI setting with the
actual1.2M transaction cap. No deployment or production/main edits occurred.
Global recovery, adaptive full-view ZK and resource-bounded FS keep their prior
status; these rewrites neither remove checks nor supply security bits.

## Next bounded experiment

Keep this measured six-coefficient version. One concrete next target is the
first gamma coefficient: both actual prepared-table paths start at QM31 one,
whose four M31 limbs are `[1,0,0,0]`. The current generic C1 dot still multiplies
all four limbs. Test a guarded specialised first chunk, with the original
generic fallback for arbitrary prepared tables. That preserves the existing
maximal-limb tests without assuming an arbitrary `from_full_table` input starts
at one. Prove the branch identity and integer bounds, count the added guard,
then compare full SBF transactions; reject it if code growth/branching outweighs
the omitted products. The already disproved four-channel fusion is not revived.
