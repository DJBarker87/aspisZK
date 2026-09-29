# R48: full-support point and relation functionals

Base `7e78e04991e6e82411852e0f201323fc96cbf8cb` (R47).
Branch `research/v8-r48-full-point-functional-20260929`.

## Result

**21 new Lean theorems compile with standard axioms only.** The actual
T163 inverse pairing, source-shaped original-table point weights, chord
transpose and image updates now use a common full-support functional.
The normalized algorithmic columns from R46/R47 have point and all seven
relation-coefficient equations in that model.

This is exact-field source-shaped semantics, **not Rust word extraction**,
a complete residual-rank theorem or a full privacy proof. No protocol or
verifier changes; no new Rust or SBF execution. The retained measured CU
endpoint remains **1,620,236 / 1,621,719**, with both 1M-cap runs exhausted.

## Exact boundary

For any quotient supported on coordinates below 128, its source chord
output is zero at coordinates 131 and above. The inverse T163 pairing is
therefore exactly the sum over **all 131** lower output coordinates, with
code weight

```
w[order(j)] - (if order(j) is inactive then w[1023] else 0).
```

This holds for arbitrary original-table weights `w`; it does not require
an honest-generation premise. The source bit-product tensor equals the
retained mathematical tensor. Applying that equality gives the original
point functional, including its balancing-pivot subtraction.

The adjoint theorem then identifies each source transposed weight below
128 with the sum of these 131 code weights against the exact sparse chord
entry. All three image updates at 1021, 1022 and 1023 are retained in the
definition. Their values at an index below 128 are zero by inequalities;
they have not been deleted or presumed redundant.

The block-kernel theorem preserves the source reversed-slot convention
`[0,3,2,1]` and the quarter factor. It proves the 256-block convolution
equals the 32-block convolution for these corrections. It is valid for
every coefficient index, hence for all seven sent/reconstructed positions,
either channel, arbitrary image challenge and arbitrary original weights.
The last bridge substitutes the **same source-normalized column** already
used by R47's raw, OOD and final-value results, for every distinct 22-root
tuple. It does not assert those source observations are now all zero: the
point and relation rows are the residual system still to be solved.

The retained R43 point witness is now justified with the enlarged model:
the extra 20 code weights, at 111 through 130, vanish for each of its three
point tensors. Their fixed sparse formulas consequently remain exact for
all quotient coordinates below 128. This fact is only about those three
point tensors at the fixed algebraic specialization. It does **not** erase
the separate sparse-G term at code coordinate 128, nor assert that the
specialization is an accepted transcript prefix.

| Leaf | New theorems | Boundary |
|---|---:|---|
| `FullPointFunctional` | 6 | Tensor identity, T163 pairing, safe 131-coordinate restriction |
| `FullQuotientWeights` | 3 | Full chord-transpose entries and image-update support |
| `FullCoefficientBoundary` | 3 | Exact block kernel and 256-to-32 block restriction |
| `FullResidualBoundary` | 5 | Point pairing and normalized source-column equations |
| `FullWitnessPointCode` | 4 | Old point certificate reuse after checking its added tail |

Five retained transport/chord/original-weight leaves compile as prerequisites;
their 16 axiom audits are not counted as new theorems. H1 active-zero,
G free active coordinates, C1 negative regressions, both pre-beta channel
messages and the posterior target `b - B A^-1 a` remain separate.

## Executed evidence

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r48_evidence.py
```

The gate passes: **23 artifacts**, **247 pins**, all **243** final cache
objects' source hashes and the unchanged R47 pin manifest checked.

- New leaves: **5.85 s** combined wall time; with retained prerequisites:
  **10.27 s**. Successful peak RSS: **2,380,812 KiB**.
- Each successful target: exit 0, swap 0, audits containing only
  `propext`, `Classical.choice`, `Quot.sound`.
- Pinned cached Lean 4.32.0 on the NUC, serial scopes:
  `MemoryHigh=3G`, `MemoryMax=5G`, `MemorySwapMax=0`, `TasksMax=128`.
- Exact target commands, base/source revisions, time, RSS and axioms are
  recorded per target. Three failed local plumbing attempts are retained;
  all were replaced without raising resource or heartbeat limits.
- The only new concrete field check is 3 by 20 fixed tensor-tail cells,
  after the generic support and transport arguments. No large recurrence
  or concrete chord graph is normalized.

## First remaining proposition

Instantiate the **full original ordinary/G weight materialization** in
this 131-coordinate model and identify its fixed specialization with R43's
`wr` and `wg`, retaining

```
hg(r) = half^10 * chordEntry(half, 7, 5, -5, r, 128).
wg = 25*e1 + 125*e2 + 5*hg.
```

The new theorem accepts any original `w`; it does not yet prove the sparse-G
source construction produces that particular `w` or prove the actual point
constructor's correspondence to the three residual point arrays. After
those source instantiations, connect the enlarged symbolic residual matrix
to the retained nonzero specialization and prove **its own** challenge
polynomial degree. The old 1,105 bound is not automatically applicable.

Still open beyond that: source sampler and canonical word/prepared-kernel
refinement, all joint residual/semantic and H1 obligations, coherent
pre-beta extraction, seed/commitment/shared-oracle laws, and adaptive visible
failure/retry/publication accounting. No independent-challenge or new hiding
assumption has been introduced. Full privacy and soundness closure are not
claimed, and supported-budget execution remains unresolved.
