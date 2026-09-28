# R35: universal leading coefficients for the low factor basis

Parent `37c3eeb9c831a2cdc3590e4afbbea5ea2b74dee1` (R34).
Branch `research/v8-r35-factor-leading-20260929`.

**Result:** the source-shaped carry/scatter model now proves the factor
basis determinant is `half^269` for **every list of 22 field roots**.
R34's determinant-scale premise is discharged for this explicit model.
No distinctness, random challenge, sampled-prefix, or residual-rank premise
is needed for that equality. This is not a proof that the observation
minor has full rank, nor a complete Rust semantics or privacy proof.

## The actual recurrence covered

`FactorLeading.lean` imports the retained `weightedIndexLoop` and
`sourceEdges`, rather than replacing the carry operation with an assumed
polynomial multiplication oracle. The relevant pinned Rust helper is
`r28_source_helpers::times_x`, which exposes its unchanged `xt` loop:
for each input j it clears successive low set bits, multiplies the running
scale by half, scatters to each cleared index, then scatters to the next
index obtained by setting the first zero bit.

For j=0..25, the proof checks only the **integer** schedule's unique edge
to j+1 and its exponent. These are the exponents

```
0,1,0,2,0,1,0,3,0,1,0,2,0,1,0,4,0,1,0,2,0,1,0,3,0,1.
```

The 27-column integer growth check establishes that no edge from j goes
above j+1. The imported weighted-loop theorem transfers those facts to
arbitrary field values. Thus for an n+1-entry input, n<26, the output at
n+1 is exactly `q[n]*half^edgeExponent(n)`; every output above n+1 is zero.
There is no concrete field recurrence reduction or expanded determinant.

Define the source-shaped factor recurrence by starting with `[1]` and
repeatedly applying `times_x(q)-root*q`. Its recursive list order is the
reverse of a left-to-right source fold; the theorem quantifies over every
root list, so this changes no leading-coefficient claim.

Induction proves both support and leading coefficient through degree 26:

```
factor(roots)[r] = 0                          when r > length(roots)
factor(roots)[length(roots)] = half^E(length(roots))
E(0)=0; E(n+1)=E(n)+edgeExponent(n).
```

The subtraction by the current root cannot affect the new leading
coordinate because the previous factor is supported strictly below it.
This is proved, not assumed to follow from monicity in another basis.

## The 13-by-13 change matrix

The matrix is explicitly defined from the factor recurrence. Entry (i,j)
is zero between different channel slots; otherwise it is coefficient
`22+i/3` of the factor with j/3 additional zero roots. These added roots
apply the source-shaped `times_x` operation j/3 times.

Support proves upper triangularity. The diagonal consists of the leading
coefficients at degrees 22,23,24,25 (three entries each) and degree 26
(one entry). Their exponents are 19,19,22,22 and 23, respectively. The
triangular determinant theorem yields

```
det(changeMatrix(half, roots)) = half^269.
```

Over a field with nonzero half, R34's basis-change lemma then gives, for
any 13-by-13 D,

```
det(D * changeMatrix) != 0  iff  det(D) != 0.
```

Unlike R34's generic lemma, this bridge does not take the change-matrix
determinant as a premise. But `D * changeMatrix` being the actual residual
factor matrix still requires the normalized-remainder/source-functional
correspondence. R34 source-tested that identity on two genuine prefixes;
R35 does not silently promote those tests to a universal Rust theorem.

Repeated roots, zero roots, and zero half are all allowed in the ring
determinant equality. Only the nonzero-equivalence corollary excludes zero
half. None of these statements assumes any law for source sampling.

## Compile and evidence boundary

All **13 new declarations** have final `#print axioms` audits containing
only propext/Classical.choice/Quot.sound. No sorryAx or added axiom.

| Final target | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| `AspisV8R19/FactorLeading.lean` | 0 | 1.49s | 2,325,688 | 0 |

Eighteen predecessor objects were reused by source hash and Lean 4.32
toolchain pin. The first compile exposed local simplifier/coercion/syntax
errors; those were repaired without weakening statements. Its failed log
is retained. The second compile passed. The final compile adds the one
missing helper's explicit axioms audit; there was no package-wide replay.

NUC scope: MemoryHigh3G, MemoryMax5G, MemorySwapMax0, TasksMax128.
Workspace `/home/dombarker/project-offloads/aspis-r35-lean-20260929-c`.
Seven public evidence artifacts plus their checksum manifest are retained
under `evidence/r35-factor-leading`. All 189 R34 host/source pins were
revalidated unchanged. No unchanged Rust elimination, proof generation,
SBF build, or CU suite was rerun.

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r35_evidence.py
```

## Next source/security obligation

The normalization factor is no longer the obstacle in the explicit model.
The next substantial object is the **observation matrix**: source-bind its
entries through the actual T163 inverse, statement-point carry operation,
and full seven-coefficient relation polynomials; prove the resulting
residual determinant polynomial nonzero, then account for its exceptional
set under the real chronological shared-oracle law. An invertible change
of coordinates does not establish sufficient observation rank.

H1 compatible-image coverage, adaptive posterior-preserving simulation,
pre-beta pair extraction, seed/commitment hops, failures/retries/publication,
and justified security losses remain open. No full privacy claim is made.
The selected verifier is unchanged at **1,620,236 / 1,621,719 CU**, with
both actual 1M runs exhausting. No merge, deployment, or wallet operation.
