# R28: retain the ordinary first polynomial with existing H1 freedom

Parent: `1106f4586fa7296d721dcbb115627fe811dc0621` (R27).
Branch: `research/v8-r28-h1-relation-capacity-20260928`.

**Result:** on both retained genuine source prefixes, the existing H1 kernel
can realize every first-relation polynomial satisfying its two necessary
linear constraints. Both complete opposite-witness source audits pass after
using this freedom to make the ordinary first polynomial identically zero.

This changes the host-only correction construction, **not the protocol,
verifier, sampler, wire format or mask distribution**. It is not the failed
H1-only semantic schedule search: sparse G still supplies the 271 semantic
coordinates. No new hiding assumption, nonzero-beta assumption, resampling or
removal of a negative regression is involved.

## Why this is the next step after R27

At beta=0, G cannot cancel a nonzero ordinary first-relation polynomial.
R27 proved that obstruction for a fixed R correction; it did not prove that
all legal R corrections fail. R28 uses spare H1 freedom to choose a better R
correction before the existing G witness audit.

Let A be the actual 562-row H1 observation matrix on the source's 1,022 legal
quotient coordinates. Its rows retain the 214 active helper coordinates,
inactive sum, 88 raw values, three point claims and 256 first-fold values.
Let P map the quotient correction to its seven-coefficient ordinary first
relation polynomial using the exact source `polynomial_for_extension` and
ordinary transported/image weights.

For x in ker A, the earlier scalar claim and final array are zero. Therefore
P(x) has boundary 4(c0+c4)=0 and evaluates to zero at alpha. After c4=-c0,
the remaining six coordinates satisfy the single equation

```
(1-alpha^4)c0 + alpha*c1 + alpha^2*c2 + alpha^3*c3
                    + alpha^5*c5 + alpha^6*c6 = 0.
```

Its evaluation covector is never zero: if alpha=0 the first entry is 1;
otherwise the second entry is nonzero. This defines a five-dimensional
candidate target space at every alpha. That algebra does **not** prove the
source H1 kernel maps onto that space at every prefix.

## Executed fixed-prefix certificate check

`stage_r28_h1_capacity.py` validates all 182 R27 pins, includes the actual
field/sumcheck/basis/weight/mask sources, and copies five helper functions
verbatim from the pinned coupled audit. It extracts the 21 public field
values and 22 actual query IDs already emitted by successful R27 verification.
No beta, alpha, query or upstream challenge is substituted.

The checker builds A plus the six source polynomial rows and performs one
incremental elimination, retaining the baseline-rank boundary. Per prefix:

- baseline rank **540**, augmented rank **545**;
- five explicit 1,022-coordinate preimages, with public binary certificates;
- **2,840** original matrix equations rechecked;
- all five complete source polynomials equal their target, including c4;
- five actual H1-padding API checks, 440 raw, 15 point, 10 OOD and 1,280
  final-coordinate zero checks;
- five corrupted-certificate negative controls rejected.

The source checks are independent of the reduced matrix. Raw/OOD checks use
the pinned source evaluation covectors; the subsequent complete witness audit
also checks actual encoded messages and decodes the G quotient independently.
The binary certificates are public linear-system solutions, not task keys or
private witness exports.

## Actual opposite-witness integration

`stage_r28_affine.py` modifies only the host witness audit and its call site.
It adds six equations with targets `-P(rq)/gamma^26` to the existing H1 solve.
All earlier checks remain; all seven coefficients of the resulting ordinary
polynomial are explicitly checked to vanish. H1 now has 568 equations,
rank 545 and 23 compatibility residuals.

Then the unchanged source semantic enumeration and 626-row G solve run with
that new H1 correction. **Both worlds pass**, with G rank 602 and all existing
source checks retained:

- same-public, opposite selected input and actual helper reconstruction;
- C1 raw/point/OOD correction;
- all 271 semantic coordinates, including the initial claim;
- both p0/p2 channel messages;
- all seven combined first-relation coefficients and Final256;
- raw, point and OOD G values, plus independent encoded-quotient decoding.

The regenerated honest proof hashes are unchanged:

```
world0 0f90e0670d5c7cedf1bea159640016eeec1574ac0de89dc94d83dd9255f07da7
world1 ca868e8f9495e06368ecaa712486befecbfaadc6ab38e8caddf38e368134ca71
```

Both are accepted by actual host replay. These remain **fixed-prefix witness
corrections**, not a causal simulator or a new source-generated beta=0 trace.
In particular, this run does not establish an admissible beta=0 prefix's H1/G
compatibility merely by retaining other values from a nonzero-beta prefix.

## Focused formal result

`lean/AspisV8R19/H1RelationLift.lean` compiles five generic leaves:
`certificate_lift`, `affine_repair`, `evaluation_covector`, `pivot_exists`,
`solve_pivot`.

They establish linear lifting from stated finite certificates, composition
with an earlier affine correction, the exact evaluation covector, its
nonvanishing, and solving its pivot equation. Rust/source linearity and
source-wide existence remain external obligations. There is no Lean claim
that the binary certificates were kernel-replayed or that all source prefixes
have rank 545. The previous R27 zero-beta obstruction remains valid for a
fixed nonzero R polynomial; R28 addresses the choice of R, not that theorem.

## Execution receipts

All runs used the cached NUC workspaces. Rust ran optimized/offline/locked,
jobs 2, with release overflow checks enabled. The expected arithmetic work
was matrix construction followed by named elimination, not proof search.
Each Rust invocation was in a 5 GiB high / 7 GiB max / zero-swap scope;
Lean used 2/3 GiB and zero swap. No task exceeded the caps.

| Focused target | Exit | Wall | Peak RSS (KiB) | Swaps |
|---|---:|---:|---:|---:|
| Capacity Rust compile | 0 | 18.83 s | 518,992 | 0 |
| Capacity world0 | 0 | 1.34 s | 23,760 | 0 |
| Capacity world1 | 0 | 1.33 s | 23,760 | 0 |
| Integrated host compile | 0 | 26.19 s | 521,868 | 0 |
| Full affine world0 | 0 | 34.85 s | 262,052 | 0 |
| Full affine world1 | 0 | 35.16 s | 261,844 | 0 |
| `H1RelationLift.lean` | 0 | 1.67 s | 1,897,144 | 0 |

Lean 4.31, source base R27 above. All five `#print axioms` results contain
only subsets of `propext`, `Quot.sound`, `Classical.choice`; no `sorryAx`.
An initial capacity compile failed because the mask API was imported from
the statement crate rather than the actual prover source (exit 101, retained
log). The corrected checker includes that actual source and its dependency.
An initial affine launch found the runner absent on the NUC; it started no
build. Copying the existing runner resolved that tooling error.

Evidence: `evidence/r28-h1-relation-capacity/`; integrity checker:

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r28_evidence.py
```

## Exact remaining boundary

The next source-specific proposition is **joint target compatibility at all
admissible source prefixes**: a legal H1 correction retaining the earlier
observations and cancelling the necessary ordinary polynomial must coexist
with a G correction retaining the recomputed semantic offset, p0/p2, raw/OOD/
point/final observations and first relation. This must include beta=0 and
other degeneracies, or identify an actual source exception and justify its
loss under the shared-oracle law. Requiring rank 545 everywhere is not a
substitute: degenerate prefixes can have a smaller necessary target space.

After that, posterior-preserving adaptive construction, coherent pre-beta
extraction, shared-oracle/seed/commitment correspondence and retry/publication
accounting remain separate obligations. Fixed-block hiding and the retained
C1 negative regression are not promoted to full-transcript privacy.

**No CU improvement is claimed.** The selected unchanged R27 verifier remains
**1,620,236 / 1,621,719 CU**, and both actual 1M runs still exhaust. No SBF
rebuild or unchanged runtime regression was repeated for this host-only
correction/proof change. The full-privacy and under-1M goals remain open.
