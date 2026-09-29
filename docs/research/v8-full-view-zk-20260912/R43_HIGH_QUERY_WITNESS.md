# R43: a fixed residual witness invariant under every low query repair

Parent `0ffa62b927c35a499f15e3412cffb643803ab7ca` (R42).
Branch `research/v8-r43-query-coverage-scrutiny-20260929`.

**Result:** a new 13-dimensional correction witness has a kernel-checked
nonzero matrix. Its matrix is unchanged under **arbitrary** changes to
quotient coordinates below 88. Thirty-nine new Lean theorems compile with
standard axioms. This supplies a concrete route around the small query-domain
bound, but the universal root-kernel/source composition is not yet proved.

No production protocol, verifier, masks, commitments, transcript, sampler,
or negative regression changed. This changes the proof's choice of correction
directions. No SBF rerun or CU saving: the selected endpoint remains
1,620,236 / 1,621,719 CU, with both actual 1M-cap runs exhausted.

## Why this is stronger than another sampled rank

R42's degree/minimum-support bound is too weak for privacy closure. The
useful alternative is a witness that works independently of the query roots.
R30 already constructs normalized query-kernel directions of the form
`E_d - R_d`, where the remainder has degree below 22. Therefore the
correction to the four-slot quotient is entirely below coordinate 88.

At the new sparse specialization, every relevant weight vanishes below 88.
Consequently **every such low correction**, not just four tested schedules,
leaves the selected observation matrix unchanged. `HighWitnessTransport`
proves that statement, including all selected polynomial coefficients and
the necessary first sparse-G boundary term.

The remaining formal premise is exact and narrow: the actual normalized
root-divisible source construction must supply the selected columns with
these high coordinates, legal support, zero G core, and the retained raw,
fold, OOD, balance and image conditions. R43 does not replace that construction
with an axiom or claim the source bridge is already discharged.

## The fixed specialization and selected directions

Over the retained M31 model, use

```
z = [0,0,0,1,1,0,0,1,0,2]
kappa = 5; alpha = 7; u = 2; v = 3
normalized chord (a,b,c) = (7,5,-5).
```

This is an algebraic witness, **not an accepted transcript**. In particular,
the base-field circle parameters are outside the deployed OOD support.
Their role is polynomial nonvanishing after the appropriate formal lift,
not a substitute for source-generated proof evidence.

Let B,C,D be the three nonconstant quotient channels, with
`A = -alpha B - alpha^2 C - alpha^3 D`. The selected direct high units are:

- B,C,D at each degree 24,25,26,27 (12 directions);
- D alone at degree 31 (one additional direction).

These are kernel-column labels `[6,7,...,17,29]` in the R30 ordering
starting at degree 22. Rows are the retained
`[1,2,3,4,5,6,7,8,10,11,12,13,15]` residual observations.

The additional direction has only `q[124]=-alpha^3` and `q[127]=1`
before the low raw repair. Although it exceeds the previous conservative
support cutoff, its chord coefficient at code coordinate 128 is zero.
Its remaining chord tail stops before the next G read at 131. Thus it
preserves all 271 G coins in the source checks. A blanket permission to use
the other two degree-31 channels would be wrong; they are not included.

The source determinant is **2079196465**. Lean proves nonzero by checking a
right inverse, not by assuming that executed determinant residue.

## Sparse weights, with the real G boundary term retained

The three point tensors have original-coordinate supports

```
point0: 100 -> -1, 101 -> 2
point1: 100 -> -2, 101 -> 1, 102 -> 4, 103 -> -2
point2: 104 -> -1, 105 -> 2.
```

These rows are fixed by the current T163 map. `SparseHighWitness` checks
their code weights against `ResidualModel` and `ResidualPins`, and proves
the resulting chord-transposed weights `e0,e1,e2` symbolically for every
output coordinate. It separately checks that they vanish below 88.

For quotient coordinates below 128, the actual ordinary/G weights are

```
wr = 5*e0 + 25*e1 + 125*e2
wg = 25*e1 + 125*e2 + 5*hg
hg[r] = half^10 * chordEntry(half,7,5,-5,r,128).
```

`half^10` is the coefficient of structured coin 0 in the retained ten-round
mask functional. Later sparse reads start at 131, outside the chord support
of these low units. `hg` also vanishes below 88.

**A source/model mismatch was caught and fixed here.** The first Lean matrix
comparison omitted `hg` by extending the old below-108 formula too far. It
rejected exactly three selected entries in the new degree-31 column. Keeping
G coins unchanged means the final scalar G functional is unchanged; it does
not make every first-polynomial coefficient contribution vanish.

The corrected formula matches all 256 low ordinary/G source weights. The
negative control shows that dropping `hg` changes polynomial coefficients
2,3,5,6; three of those occur in the selected minor. The failed Lean log is
retained. No source check was weakened to obtain the fixed certificate.

## Exact formal boundary

The 19 focused files establish 39 theorems:

| Component | Theorems | What is checked |
| --- | ---: | --- |
| `HighRepairInvariant` | 5 | Unit-column/source-kernel identities; point and polynomial invariance under whole-low-block repairs |
| `SparseHighWitness` | 10 | Three actual-model code shapes, their point weights, and four low-support zeros including `hg` |
| Generated matrix/inverse leaves | 17 | All 169 model entries, all 169 inverse-product entries, and nonzero model determinant |
| `HighWitnessTransport` | 7 | Weight support, direct-column observations, and the unchanged nonzero matrix for arbitrary low repairs |

The terminal theorem quantifies over any family
`q : Fin 13 -> (Fin 32 × Fin 4) -> M31`. If each q agrees with its selected
direct column on block indices at least 22, its selected matrix is exactly
the fixed invertible matrix. There is no probability, fresh-oracle, root
distribution, or hiding assumption in this theorem.

This theorem is not yet an exact-QM31 universal-source residual-coverage
theorem. The field lift, normalized root section, exceptional boundary
direction, full compatible-image dependencies and source refinements still
need to be composed. In particular, the Schur RHS `b - B*A^-1*a` remains
mandatory; this witness does not authorize dropping posterior information.

## Source checks and rejected approaches

All executions use the pinned source and optimized release arithmetic.
The targeted roots are four valid, distinct 22-index schedules: eleven
opposite pairs, 22 unpaired roots, spaced opposite pairs, and five quartets
plus a pair. They are controlled algebraic/source checks, not accepted
public prefixes or distribution experiments.

1. With eight full-QM31 challenge assignments per schedule, the old minor
   has rank 13 even for the opposite-pair symmetries. This rejects the
   particular symmetry obstruction tested, not all possible obstructions.
2. Boolean sparse specializations and two one-parameter sparse families
   fail to reach rank 13 using only degrees 22..30. Their rank-12 (or lower)
   results remain in the ledger; they are not privacy attacks.
3. Adding only degree-31 D gives rank 13 in all 32 tested cases of the
   second sparse family, while all G coins remain zero.
4. The final fixed witness is compared against all 3,072 source-transposed
   point weights and 256 low ordinary/G weights. For all four schedules,
   28 normalized remainder-corrected directions match their direct units
   in all 17 observations: **112 columns, 1,904 equality checks**. There
   are **2,440 changed low coordinates**, so this is not a vacuous check
   with the query correction omitted.

The source witness JSON is identical before and after the explicit boundary
formula check. The generated Lean matrix is therefore certified against the
original source calculation, not a replacement calculation chosen to pass.

## First remaining proposition

Compose the retained natural-basis root-kernel construction with this new
section for **every** distinct 22-tuple of actual source roots:

1. Normalize `E_d` by subtracting its degree-below-22 remainder for
   d=24..27 and d=31; prove the source-coordinate agreement above 87.
2. Prove the added D31 direction and every low repair preserve the G core,
   together with raw/final/OOD/balance/image conditions.
3. Lift the constant witness into the exact QM31 field and the new residual
   polynomial. Prove nonvanishing with query roots fixed, and its degree in
   the remaining challenges.

The supplied invariant and inverse close the fixed-matrix part, not these
whole-source steps. After them, the actual shared-oracle conditional law,
bounded sampling failures, observer first hits, retry/publication accounting,
H1 joint coverage, adaptive posterior simulator, coherent pre-beta extraction,
and seed/commitment hops remain. Full privacy and soundness closure are open.

## Resources and receipts

Final successful focused Lean leaves total **28.83 s**, peak RSS
**2,879,012 KiB**, swap 0. All 39 audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Per-target commands, source hashes,
exit codes, time and RSS are retained. Lean used 3G/5G/no-swap scopes and
the existing 4.32 cache. No large root recurrence was normalized.

The final source checker compiles in **19.13 s**, peak **518,092 KiB**,
and runs in **0.03 s**, peak **2,112 KiB**, both exit 0/swap 0. Rust used
release, locked/offline, two jobs, overflow checks, and 5G/7G/no-swap scopes.
Simultaneous reservations never exceeded 12 GiB on the 62-GiB NUC.

Retained failures include two incorrect import paths, local Lean syntax/sum
plumbing, the substantive three-entry omitted-boundary mismatch, a Rust index
type error, and an incorrect negative-control count (three selected entries
versus four full polynomial coefficients). None was a resource failure.

The focused runner now invalidates transitive local dependents when an
import changes. Data/entry/inverse dependents were explicitly rebuilt once
after the corrected weight model, rather than relying on source-hash-only
cache reuse across that change. This was a cache-validity correction, not
an unchanged full regression.

The 81-artifact evidence manifest is checked by
`tools/check_r43_evidence.py`; the 16 generated certificate files are also
checked by `generate_r43_certificate.py --check`. Every per-experiment
198-pin source manifest retains the old 197 pins unchanged except additive
host Cargo entries and one new host checker. No merge, deployment or wallet
operation occurred.
