# R47: circle evaluator, raw openings and prepared fold

Base `3cd200321280562f05514a9f8dfa0b713cb25d53` (R46).
Branch `research/v8-r47-circle-opening-bridge-20260929`.

## Result

**30 new Lean theorems compile with standard axioms only.** The bit-selected
circle evaluator is now connected to the four normalized quotient channels,
the T163 mask transport, chord division and the prepared polynomial fold.
For the same R46 algorithmic correction, all four queried raw values vanish
and the folded quotient value vanishes at every admissible circle fibre.
The existing balance, sparse-G coin and two OOD identities use this same
evaluator rather than a separate unconnected channel formula.

This is a composition of **exact-field source-shaped semantics**, not Rust
machine-word extraction. In particular, the source sampler's group/point
premises and the prepared multiplier/lazy-reduction implementation have not
been proved by this work. Full privacy, soundness closure and supported-budget
execution remain open. No production/protocol/verifier changes or new Rust/SBF
run; CU remains **1,620,236 / 1,621,719**, with both 1M-cap runs exhausted.

## What is proved

For `r < 1024`, the source-style product over the ten selected bits equals

```
naturalLineValue(x, r / 2) * (if r is even then 1 else y).
```

The factor sequence is exactly `[y,x,T2(x),T4(x),...]`. The bit-selector
identity uses a symbolic proof about `bitIndices`, bitwise AND and powers
of two. It does not enumerate 1,024 field expressions or assume a selector
table has the right meaning.

For the flattened four-slot coefficients, the serialized evaluator equals

```
A(T2(x)) + y*B(T2(x)) + x*C(T2(x)) + x*y*D(T2(x)).
```

The four fibre slots retain the source order
`(x,y), (x,-y), (-x,-y), (-x,y)`. The negative-x doubling identity and all
four signs are proved, rather than treating the slots as interchangeable.

On `x^2+y^2=1`, the transported mask's opening is the quotient opening
multiplied by `L(x,y)=a+b*x+c*y`. Consequently:

- At any supplied query root `T2(x)=t[j]`, all four raw mask changes are
  zero. Raw-zero preservation itself needs no chord inversion.
- When each of the four chord denominators is nonzero, division recovers
  the exact quotient value at that slot.
- With `x != 0` and `y != 0`, the normalized fold equals the coefficient
  contraction `A + alpha*B + alpha^2*C + alpha^3*D`, which is zero for the
  constructed column at every block.
- The retained prepared polynomial implementation's constant, linear,
  quadratic and cubic arithmetic equals that fold, including the second
  pair's **negative** y-inverse. Its machine implementation is separate.

The folded-value theorem is pointwise for every admissible circle fibre.
It is not relabelled as an extracted proof of every subsequent FFT, array
serialization or committed Final256 operation.

| Leaf | New theorems | Boundary |
|---|---:|---|
| `CircleWeightBridge` | 8 | Symbolic source-bit selection and natural circle weights |
| `CircleChannelsBridge` | 7 | Flattening, complete four-channel evaluation and root zero |
| `CircleObservationBridge` | 8 | Fibre signs, mask/chord evaluation, division and fold zero |
| `PreparedCircleFold` | 2 | Prepared polynomial arithmetic and folded-mask zero |
| `SourceCircleBoundary` | 5 | R46 algorithmic columns, raw fibre, final scalar, balance/coins/OOD |

The retained `V5FriNaturalBasisRadix4.lean` is copied byte-for-byte, compiled
once and audited separately. Its declarations are not counted as new work.
H1's active-zero condition is not imposed on G, and no masks are resampled.

## Source pins and executed evidence

The source evaluator helper remains pinned through R43's stage manifest:
`r28_source_helpers.rs` SHA256
`ea1d0cad89a944b0a6edbf1fdbcc5517ff39ce00e7bb427bb58c698cf646b802`.
The source circle/prepared-fold file is pinned to
`77625499c80b30fe9de1e79daaf35dc964bf0cb675a65ced69592d3d421c856b`.
The retained radix proof's SHA256 is
`0641318603afdaf3f1b1bf9b66c418da67049160973348468f4c3fafadefa4dd`.

Run:

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r47_evidence.py
```

The gate checks **21 artifacts**, **238 source pins**, the unchanged R46
pins, and all **233** final cached objects' source hashes.

- New leaves: **5.94 seconds** combined wall time.
- Including the retained radix leaf: **7.08 seconds**.
- Successful peak RSS: **2,341,924 KiB**; every successful target exit 0,
  swap 0, and only `propext`, `Classical.choice`, `Quot.sound` in its audit.
- Serial NUC cached Lean 4.32.0 scopes: `MemoryHigh=3G`, `MemoryMax=5G`,
  `MemorySwapMax=0`, `TasksMax=128`. No unchanged Rust/SBF suite rerun.
- Exact commands, source/base revisions, time/RSS/swap and axiom output
  are retained per target under `evidence/r47-circle-opening-bridge/`.

The first selector attempt reached the normal heartbeat limit. It was
replaced by the general symbolic bit-index proof, not split into a larger
concrete field replay or given higher limits. Other retained failures were
finite-index coercion/rewrite plumbing. No sorry or failed object enters
the final successful cache.

## First remaining proposition

Bind the remaining **original-table point claims and first relation-polynomial
coefficients** to the same transported normalized columns, for symbolic
source challenges. In particular, prove the actual T163 inverse pairing
against the statement's tensor weights equals the code-coordinate pairing,
then safely restrict the chord output to coordinates below 131. Do not
reuse the old 111-coordinate generic residual model for the degree-31 D
direction without proving its omitted terms vanish or retaining them.
The first sparse-G boundary contribution must remain.

That source-functional identity must feed the new fixed-query residual
matrix, its nonvanishing specialization and its own degree bound. The old
1,105 degree bound is not automatically a bound for this new polynomial.
Preserve the posterior target `b - B A^-1 a` throughout.

Additional open source/release obligations include formal refinement of
the actual sampled fibre coordinates (R42's exhaustive source checks are
not a Lean extraction), canonical word/prepared kernels, all joint residual
and semantic equations, H1 coverage, coherent pre-beta extraction,
seed/commitment/shared-oracle laws and adaptive failure/retry/publication
accounting. No independent-challenge or new hiding assumption was introduced.
