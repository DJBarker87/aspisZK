# Component OOD binding interface

Research-only extension at `51b78cbf7fadee4ec70328c86add7678a43f21da`,
with the same pinned borrowed formal cache
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Status: **kernel-checked deterministic interface**. The successful
[v4 log](experiments/component-ood-binding-v4.log) records exit 0, 6.17 seconds,
5,636,030,464 bytes peak RSS and zero swaps. All five printed declarations
use only `propext`, `Classical.choice` and `Quot.sound`.

The new interface connects the **two circle OOD vectors** in `Data.answers`
to a recovered component tuple. These are not the three ordinary point rows
already treated by `ComponentRows`.

`circleFunctional x y` is constructed as a genuine linear map on the actual
natural1024 message: take its low-bit even/odd coefficient projections,
apply the natural line-polynomial linear map, evaluate at x and add y times
the odd value. `circleFunctional_apply` identifies that constructed map
with the literal `circleEval(initialP0 message,initialP1 message,x,y)`.
Linearity or an encoder equality is not an assumed premise.

For checked source inverse data, both OOD points on the circle, and the
literal two image conditions, `original_point_values` derives

```
circleFunctional(point_r)(d.original Q) = sum_lane gamma^lane * answers[r,lane].
```

It uses the actual chord vanishing at its defining points, the proved
natural reconstruction identity, and the checked sparse interpolant. The
equal-x branch retains its y-coordinate interpolant. No individual answer
is assumed correct.

If recovery identifies `d.original Q` with `batch gamma p`, the new
`recovered_ood_error_eval` theorem derives that the actual component-error
polynomial vanishes at gamma. The retained scalar-power lemmas give degree
at most 28, and prove this polynomial nonzero whenever an individual answer
differs from the literal circle evaluation of that component message.

This is deterministic algebra, not a new probability claim. Charging a
28-root exceptional set requires p, the particular OOD point and its answer
vector to be fixed before a fresh gamma, with the actual sequential OOD
timing and Fiat–Shamir resources handled separately. The general theorem
does not itself move a post-gamma tuple backward in time.

No Rust, proof-body or transcript change is made. The inherited body model
remains 40,282 bytes; there is no new disclosure or verifier operation.

## Reproduction

From this research directory, using a fresh log filename:

```
bash experiments/run_component_ood_binding.sh ComponentOODBinding experiments/component-ood-binding-v4.log
```

The runner verifies source/olean provenance before and after the focused
leaf, with `-M7000` and an independent aggregate 7 GiB guard. Exact hashes and
scope are in [component-ood-evidence.json](component-ood-evidence.json).

The first check exposed an unresolved natural `line` namespace/definition
boundary and dependent `Fin 2` vector rewriting. The replacement explicitly
uses the natural line map and proves the two literal point identities
before choosing the row. No theorem hypothesis or resource limit changes.
V2 isolated the remaining large definitional reduction in a final `rfl`;
V3 replaced it with symbolic application lemmas. The last inference issue
was the even/odd map's `2*n` dimension, settled in V4 by explicit `n=512`
applications of the retained generic lemmas. No unchanged heavy replay,
large finite enumeration, new axiom or `sorry` is used.
