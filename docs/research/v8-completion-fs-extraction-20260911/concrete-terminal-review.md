# Same-tuple compact semantic alternative

`SelectedConcreteTerminal.lean` specializes the retained compact semantic
alternative to the constructed 29 lanes of `SelectedConcreteRowLanes`.
Its focused pinned Lean 4.32 leaf now passes with standard axioms only. No new
probability bound is asserted.

The good conclusion now contains facts about one specified tuple:

- the 95 selected semantic residuals vanish through the existing 24 packs;
- all 57 blocks satisfy their eleven two-round Poseidon checks;
- the copy row equation holds on every row using this tuple's H (component 26);
- the sum of H and its inactive-selector weighted sum are zero.

The last two facts are **derived on the good branch**, not supplied as global
helper hypotheses. Copy denominator nonpoles remain a separate obligation.
The theorem does not turn the copy row alone into `CopyConditions`.

## Complete retained alternative

`concrete_terminal_alternative` leaves these alternatives intact:

1. the concrete good conclusion;
2. `badTheta T (tupleLanes ...)`;
3. `badPoint (thetaTable (tupleLanes ...) theta)`;
4. the original quadratic `badMu`, with this H and active selector;
5. initial scalar differs from the mask-table sum;
6. final compact scalar differs from the reference trace's final scalar;
7. the named compact `RepairHit` in the supplied causal plan.

The final theorem removes only alternatives 5 and 6, using explicitly named
`maskBound` and `terminalBound` equalities. Neither equality is defined as Rust
acceptance, nor proved by supplying a reference trace. The unconditional
alternative is available if these producers have not been constructed.

## Premise producers still required

| Input/premise | Present status |
|---|---|
| Tuple, lambda, chi, public inputs | Explicit inputs; use recoveredComponents in a later join |
| 29 Boolean lanes | Constructed from that tuple by the preceding checked leaf |
| H | Literally component 26, not a separate supplied helper |
| Active-selector table | Explicit input; must equal selected transfer copy-active source selector |
| Mask table | Explicit input; must be constructed from C1/mask-only/G, not identified with D by assertion |
| Initial and response fields | `FixedFieldView` input; same-body parser/scalar producer join required |
| ReferenceTrace | Explicit recurrence and degree certificate; source reference-oracle construction required |
| Plan/FollowsPlan | Explicit causal interface, not inferred from a completed transcript |
| Mask binding | Initial claim must equal the exact selected mask sum |
| Terminal binding | Actual terminal acceptance plus exact point/opening/function correspondence must produce this equality |
| Allowed challenge sets | Explicit memberships; no source sampler law or ROM coupling follows |

The source terminal spells the mask as
`state_only_selected_mask_value(&c1, &mask_only, g, point)` and then adds
`eta * original` (pair_forest_semantic_terminal.rs around 1420).
Keeping `mask` explicit is intentional until that functional producer is
connected. Likewise the two helper terms appear as `mu*h1_z` and
`mu^2*(1-copy_active)*h1_z` around lines 1307–1308.

The existing aggregation theorem needs its tables fixed before theta to use
its root budget, and its point table fixed before the equality point. This
deterministic specialization does not prove those timing facts for a tuple
recovered after C2/gamma. It also does not add any probability terms or remove
replay failures. No production, transcript, proof-byte or verifier check changes.

## Next decisive producer

Construct the selected mask/active reference table and its reference trace from
the same fixed C1/C2 source execution; then join the same-body semantic scalar
with the actual terminal evaluation. This must establish `terminalBound` and
the causal plan uniformly across legal continuations. Merely assuming the
terminal equality under another name would not advance that join.

The final focused run used `-j1 -M9000` in a scope capped at 10 GiB with swap
disabled: exit zero, 3.03 s wall, 6,555,676 KiB peak RSS. Earlier namespace,
section-inclusion and reducible-`Or` elaboration failures are retained as
development evidence; the final local outcome wrapper carries the original
algebraic alternative plus a proved good-branch implication. Fresh
dependency/kernel replay was not run.
