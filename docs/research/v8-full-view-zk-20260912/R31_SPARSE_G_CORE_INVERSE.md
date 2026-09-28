# R31: explicit inverse for the query-independent sparse G core

Base revision: `331866cfbe3269add68e9ce7c8e050a5e96fdfaa` (R30).
This is host-only source evidence and a symbolic Lean proof. No verifier,
proof format, transcript, mask profile, challenge, or negative regression changed.
The selected verifier remains at **1,620,236 / 1,621,719 CU**; the actual
1M-cap runs still exhaust. No unchanged SBF suite was rerun.

## Result

The current sparse G core has an explicit invertible specialization, proved
without expanding a 271-by-271 determinant. The specialization is **algebraic**,
not a source-generated or sampler-admissible transcript. It is a route to a
nonzero polynomial minor, not a universal coverage or privacy theorem.

R30 separated the 699-dimensional balanced, raw/final-zero quotient section
from its low-degree query-dependent remainder. On its 271 G coordinates the
remainder is invisible. Its point and relation-polynomial residuals are **not**
invisible and remain obligations.

## Exact construction

Selected encoded coordinate `n(i)=128+3i`, for `0 <= i < 271`.
Choose quotient channel `k(i)=1` when `n(i)%4=0`, otherwise `n(i)%4`.
The column in R30's degree-22-through-254, three-channel ordering is

```
c(i) = 3*(floor(n(i)/4)-22) + k(i)-1.
```

Lean proves all columns are below 699 and the column function is injective.
At alpha=1, a selected quotient column has `q[4d+k]=1`, `q[4d]=-1`.
At identity chord `[1,0,0]`, the selected G map is

```
(B x)[i] = -x[i]-x[i+1]  if i%4=0,
           x[i]          otherwise.
```

The last exceptional index is 268, so its partner 269 is in range. There are
68 blocks `[[-1,-1],[0,1]]` and 135 singleton `[1]` blocks. **B²=I** over
any commutative ring. The proof uses four symbolic residue cases, not a huge
concrete reduction or an assumed rank certificate.

The source-shaped quotient model assigns the high channels of successive
groups as `{1,3}`, `{2}`, `{1}`; `source_block` proves that reading its selected
encoded indices gives B exactly. Zero extension gives a finite 271-coordinate
inverse. `SparseGChordWitness` composes this model with the retained R17
`chordCoefficient`: with chord `[a,0,0]`, its output is `a*q[r]` for any scatter
edge lists. Thus the identity-chord argument does not assume special carry
weights or discard a nonzero chord term.

For normalized chord `[1+uv,uv-1,-(u+v)]`, take `u=iota`, `v=-iota`,
`iota²=-1`. The chord is `[2,0,0]`; the inverse is `(1/2)B`.
Lean proves source-model injectivity, surjectivity and the explicit inverse
given `iota²=-1` and `2*h=1`. Those are algebraic premises, not hiding
assumptions; the Rust checker instantiates them in QM31.

**Both rational-parameter denominators vanish at this witness.** Lean proves
`1+iota²=0`, and Rust checks both denominators. This point is excluded by the
sampler. Nonzero evaluation outside sampler support can witness a nonzero
polynomial; it cannot establish a valid source prefix or its probability.

## Pinned actual-source check

Stage `/home/dombarker/project-offloads/aspis-r31-inverse-20260928-b`, 187 pins.
It is R30's 186-pin stage plus this checker and its host Cargo entry. All
inherited pins other than that Cargo manifest are identical.

For every selected input basis column, the checker runs the existing chord
function, current T163 inverse, and actual `structured_g::mixed_coins`.
It also verifies forward/inverse transport consistency, balanced/final-zero
direct quotient columns, and distinct/in-range selected columns.

| Executed check | Result |
| --- | ---: |
| Source matrix entries, identity and normalized chords | 146,882 equalities |
| Explicit B² coordinates on every basis input | 73,441 equalities |
| Missing-partner / wrong-sign negative controls | 136 detected |
| Both normalized-witness sampler denominators | zero, explicitly rejected as admissible witness |

This tests actual arithmetic routines at two algebraic specializations. It
does not generate a proof, substitute challenges, or replay the two genuine
prefixes as if their alpha/chord equalled this witness. R29's beta-uniform
source corrections and R30's genuine-prefix residual checks remain separate.

## Formal and execution receipts

The source-shaped scatter object is reused from the successful R30 cached
build after matching its source hash and Lean toolchain. No dependency build,
full certificate aggregation, determinant expansion or unchanged regression ran.
All jobs ran on the Tailscale-connected NUC with `MemorySwapMax=0`, TasksMax128;
Rust MemoryHigh5G/MemoryMax7G, Lean MemoryHigh2G/MemoryMax3G.

| Target | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Release/offline/locked host checker compile | 0 | 18.79s | 517,464 | 0 |
| `r31-sparse-g-inverse` source check | 0 | 0.04s | 2,112 | 0 |
| `SparseGCoreInverse.lean`, 12 audited declarations | 0 | 2.90s | 1,829,684 | 0 |
| `SparseGChordWitness.lean`, 5 audited declarations | 0 | 1.44s | 1,704,456 | 0 |

All 17 final axioms audits contain only `propext` and, where needed,
`Quot.sound`; no accepted `sorryAx` or added axiom. The logs retain harmless
tactic/simp diagnostics as well as exit status and audit output.

Development failures are preserved: absent legacy Omega import (no cold
build attempted); incomplete local simplification/linearity proofs; and the
host checker initially calling an unavailable `QM31::double` method. The
replacement uses the existing addition API. These failed attempts are not
accepted proof evidence. Final records name exact source hashes and commands.

Reproduction tools: `stage_r31_inverse.py`, `run_r31_inverse.py`,
`run_r31_lean.py`, `collect_r31_evidence.py`; offline artifact gate:
`python3 docs/research/v8-full-view-zk-20260912/tools/check_r31_evidence.py`.

## First remaining proposition and release boundary

The next proposition is a **current-layout polynomial/minor bridge**: the
271 selected source-shaped columns for arbitrary alpha and normalized chord
are evaluations of one fixed polynomial matrix, and this explicit inverse
makes its selected determinant nonzero, with kernel-checked degree bounds.
R17's entry/degree machinery is reusable, but its old active-row inventory is
not the current T163 inventory. This packet does not silently import that
old minor certificate as a current-layout result.

Even after that bridge, the following remain separate:

- Current H1 core and the joint H1/G residual target coverage. R30 measured
  8 H1 and 13 G additional residual ranks on two prefixes, not all prefixes.
- Rust/field/index refinement and any exceptional-source set bound under the
  actual adaptive shared-oracle law. No independent-uniform challenge law is
  assumed here.
- Posterior-preserving simulator/correction, coherent pre-beta extraction,
  commitments and seed expansion, failures/retries/publication, explicit
  soundness/privacy losses, and the full 1M execution gate.

No new protocol profile or hiding assumption, global privacy claim, CU
improvement, merge, deployment or wallet operation is part of R31.
