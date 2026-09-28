# R32: current sparse-G nonzero polynomial minor

Parent: `66727edcc16549a5dd251dc1eca3d2d2e2c57ad5` (R31).
Branch: `research/v8-r32-sparse-g-polynomial-20260928`.

**Compiled result:** the 271 selected columns of the current sparse-G
source-shaped chord map define a determinant polynomial that is not zero,
with total degree at most **1,355**. Over a field, its evaluated core map is
surjective whenever that determinant evaluation is nonzero.

This is an algebra/source-model result, not a probability bound for the
actual transcript. No Rust, protocol, production verifier, proof format,
mask profile, or negative regression changed. The full privacy goal remains
open. The selected verifier remains at 1,620,236 / 1,621,719 CU; its actual
1M-cap executions still exhaust. No unchanged SBF or Rust suite was rerun.

## What is now bound, rather than assumed

`SparseGPolynomial.lean` imports the retained R17 `ActiveEntry`,
`MinorDegree`, concrete weighted scatter/chord model, and R31 inverse.
It does **not** import R17's old active-row list or its old chosen minor.

For current encoded row `n(i)=128+3*i`, define

```
base(j) = 4*floor(n(j)/4)
slot(j) = 1 if n(j)%4=0, else n(j)%4.
```

`column_binding` proves these are exactly R31's selected columns in the
degree-22-through-254, three-channel ordering. The matrix entry is the
existing `sourceChord` on

```
q[r] = unit(base(j)+slot(j))[r] - alpha^slot(j)*unit(base(j))[r],
```

read at `n(i)`. This uses the concrete 512/513 weighted index schedules,
finite zero extensions, and source-shaped even/odd chord formula. There
is no premise asserting that an arbitrary matrix has the desired rank.

The existing six-constant entry representation supplies a multivariate
polynomial in alpha,u,v with normalized chord
`[1+u*v, u*v-1, -(u+v)]`. `entry_eval` and `minor_eval` prove its evaluation
equals this source-shaped matrix for arbitrary parameters. Entry degree
is at most 5. The retained symbolic determinant-degree theorem gives
`271*5=1355`, without enumerating determinant permutations.

The bound is deliberately conservative. No tighter column-summed or
per-variable bound is claimed by this artifact.

## Nonvanishing proof

`sparse_read` proves the selected direct unit columns have exactly the
R31 two-coordinate block pattern, by symbolic integer/index cases.
`witness_mulVec` proves that at alpha=1 and chord `[2,0,0]`, multiplication
by the selected matrix is `2*B`, where `B*B=I` was proved in R31.

The explicit inverse `(1/2)*B` therefore gives matrix surjectivity and
nonzero determinant at that specialization. For any nontrivial commutative
ring containing `u` with `u*u=-1` and `h` with `2*h=1`, the normalized
specialization `(alpha,u,v)=(1,u,-u)` has chord `[2,0,0]` and nonzero
determinant. Consequently the determinant polynomial is not zero.
These are stated algebraic premises; R31's pinned QM31 checker supplies
the concrete arithmetic witness, not a new cryptographic assumption.

As R31 explicitly proved and checked, `1+u*u=0` at this specialization.
It is **excluded by the source sampler**. Its role is to prove polynomial
nonvanishing, never to stand in for an accepted source transcript.

Finally, `core_surjective_outside_zero_set` uses the actual evaluated
determinant condition to establish core surjectivity at arbitrary field
parameters. It does not assume that this condition holds for every prefix.

## Exact formal results

All 13 new declarations are audited with `#print axioms`:

- `column_binding`
- `entry_eval`, `entry_degree`, `minor_eval`
- `determinant_eval`, `determinant_degree`
- `source_scalar`, `sparse_read`, `delta_sum`
- `witness_mulVec`, `witness_det_ne_zero`, `polynomial_ne_zero`
- `core_surjective_outside_zero_set`

Final target: `lean/AspisV8R19/SparseGPolynomial.lean`.
Final exit **0**, wall **2.80s**, peak RSS **2,306,756 KiB**, swaps **0**.
All final audits use only standard `propext`, `Classical.choice`,
`Quot.sound`; no `sorryAx` and no added axiom.

NUC output: `/home/dombarker/project-offloads/aspis-r32-lean-20260928-d`.
Source root: `/home/dombarker/project-offloads/aspis-r32-lean-src-20260928-a`.
Every command, source hash, toolchain, base revision, wall/RSS/swap receipt
and failed development attempt is retained in `evidence/r32-sparse-g-polynomial`.

The complete cached determinant/polynomial library was found in a retained
Lean **4.32.0** workspace. The eight small prerequisite leaves were compiled
once in that environment; subsequent attempts reuse their exact objects
after checking source hashes and toolchain. No cold dependency build or full
formal manifest replay was run. Lean scopes were MemoryHigh3G/MemoryMax5G,
MemorySwapMax0, TasksMax128. The changed leaf was checked first after its
necessary local prerequisites, not by a package-wide build.

The first proof attempt left local index simplification, a finite-index
coercion and a sum reassociation unfinished. Those were fixed directly;
no memory/heartbeat cap was increased. The failed audits remain evidence
of development failure, not accepted theorem evidence.

## Cache incident and recovery

The first `lake env` invocation in the exported 4.32 workspace unexpectedly
reported a Mathlib URL mismatch and replaced that dependency checkout.
The job was stopped after 41.2s, before compiling a theorem. It peaked below
1 GiB in its scope and used no swap. This was a tool-owned dependency/cache
mutation, not a project protocol/source change.

The matching retained export's tracked source tree was compared to the
replacement checkout at revision `81a5d257c8e410db227a6665ed08f64fea08e997`:
no differences. Its compiled `.lake` directory was copied back, then compared
recursively byte-for-byte: no differences. Recovery commands and exit-zero
receipts are retained. Nothing further was deleted; no key was involved.

`run_r32_lean.py` now creates a **dependency-free** focused Lake workspace
and points `LEAN_PATH` at the preserved exported caches. The collected
manifests have empty dependency lists, so Lake never resolves or replaces
those exported dependency checkouts. This also prevents a repeat of the
incident in later focused proof steps.

## What this does not close

The unchanged R31 stage still has all **187 source pins** verified; its
146,882 source-entry comparisons remain the executable source witness.
R32 proves more in the symbolic model, not a complete extracted-Rust
field/index refinement. The arbitrary-parameter bridge to the actual
transport/coin read and its complete source semantics remains explicit.

The immediate source-facing continuation is to compose the retained
rational-chord normalization/nonzero-scale theorem with this result for
admissible distinct OOD parameters, then address the current-layout joint
residual system. R30 measured 13 additional G residual dimensions and 8 H1
residual dimensions on two genuine prefixes; this new core theorem does
not waive those observations or promote their measured ranks to universal
coverage. In particular, the ordinary point changes under low query repair.

The required joint G proposition still includes every compatible semantic
coin target and cross-polynomial target, while retaining raw/point/OOD/final
values, balance and the structured-polynomial condition. H1 capacity and
its current-layout nonzero core certificate remain separate obligations.

Turning the polynomial zero set into an explicit exception probability
requires the actual adaptive shared-oracle challenge law, including
rejections and repeated addresses. No IID-uniform shortcut, simulator,
posterior law, coherent pre-beta extraction, commitment/seed hop,
retry/publication theorem or global privacy/soundness claim follows just
from this nonvanishing result.

Offline check:

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r32_evidence.py
```
