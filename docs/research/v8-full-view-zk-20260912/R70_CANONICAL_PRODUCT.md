# R70: canonical generated QM31 multiplication

Base revision: `851c10072a74fff8523b8817d791153128cf920e` (R69).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Result

The exact R69 generated `field.r24_canonical_mul` and public `field.QM31.mul`
now have a checked execution theorem for **every canonical input pair**.
The guard returns `some` of the canonical encoding of the retained QM31 field
product; the public caller returns that value, and no internal `Result.fail`
is possible. Canonicality is the four explicit limb bounds `< 2147483647`.
There is no assumed multiplication-correctness or no-failure premise.

Three leaves add 25 theorems:

- `ExplicitWord`: 13 word, checked-product, wrapping-operation, reducer and
  partial-fold facts for the actual generated R69 functions.
- `ProductExecution`: two guard/execution facts, deriving all intermediate
  bounds symbolically and executing the source into four reduced coordinates.
- `ProductCorrectness`: ten residue/field/caller facts, identifying those
  coordinates with multiplication in the retained quadratic tower, preserving
  canonicality and excluding internal failure.

R69's noncanonical guard/fallback theorem remains separate. This milestone does
not assert canonical field behavior for arbitrary noncanonical constructors.

## Source correspondence

The proof imports `AspisR69Explicit.Funs`: the exact extraction of the measured
fixed-arity helper, not the R68 diagnostic traversal replacements. Generated
bodies are unchanged; only the previously audited import narrowing is used.
The evidence checker reruns the R69 source/artifact audit, verifies the new
proof hashes, compares cached metadata, and pins transitive local sources and
the retained full Aeneas runtime objects. Its inherited runner preflight checks
R66 support; that preflight alone is **not** claimed to audit R69.

No Rust, protocol, transcript, challenge schedule, source extraction, or SBF
artifact changes in R70. Thus runtime regressions were not rerun unchanged.
Retained complete CU is **1,495,663 / 1,497,050**. Both actual 1M-cap runs still
exhaust. ELF: `412c762bb5a0190bd7f068b12fb1323e8ba84985a727b1008fe30f29550dc518`.

## Focused compilation evidence

NUC over Tailscale, Lean `leanprover/lean4:v4.32.0`, cached full Aeneas runtime.
Each target used `lake env lean -j1 -M4500` in a systemd scope with measured
`MemoryHigh=5 GiB`, `MemoryMax=7 GiB`, `MemorySwapMax=0`, `TasksMax=128`.
The final replay reused 313 compiled targets and compiled only these three.
All 25 `#print axioms` audits contain at most `propext`, `Classical.choice`,
and `Quot.sound`; no new axioms or admitted proofs.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/ExplicitWord` | 0 | 1.87 | 3,695,372 | 0 |
| `AspisV8R19/ProductExecution` | 0 | 4.18 | 3,732,564 | 0 |
| `AspisV8R19/ProductCorrectness` | 0 | 2.20 | 3,706,084 | 0 |

Focused predecessors and failed logs are retained, not presented as successes.
The execution proof initially hit the default heartbeat limit because local
aliases hid the same bound expressions from the simplifier. Normalizing those
aliases before discharging bounds eliminated the issue; the final proof uses
the default heartbeat limit. Residue transport was fixed by casting the retained
modulo equality directly into the chosen field instance, not by weakening its
statement. No OOM retry or concrete large recurrence reduction was used.

Audit: `python3 docs/research/v8-full-view-zk-20260912/tools/check_r70_evidence.py`.
Public receipts/logs/pins: `evidence/r70-product/` (60 manifest artifacts).

## First remaining proposition

Transport the unchanged R66 CM31 square/inverse execution facts into the R69
generated namespace, then prove **the complete source circle map**, including
singularity-before-subfield error ordering, using this product theorem. Compose
that with the bounded sampler and its actual observer next.

This is a theorem about pinned extracted execution, not a verified Rust/SBF
compiler theorem, full privacy theorem, or soundness release. Shared-oracle,
seed expansion, C2 commitments, the complete joint semantic/opening view,
visible failures/retries/publication, numerical loss accounting, and coherent
pre-beta quotient-pair extraction remain open. The C1 negative regression,
fixed-block hiding and local joint coverage remain distinct and unchanged.
No deployment, merge or wallet operation.
