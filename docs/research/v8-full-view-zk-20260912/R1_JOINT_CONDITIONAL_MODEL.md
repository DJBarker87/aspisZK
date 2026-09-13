# R1 joint and conditional observation model

Date: 2026-09-13. Source head: `94511feed595fbf3b68ed52f0f2f5f09e0cabcd1`.

This is the source-derived boundary for the repaired-q22 research candidate.
It is not a joint-view certificate and does not authorize publication.

## Common representation and coins

All algebraic observations are represented over M31. A QM31 value is expanded
in the source tower order `(c0.a, c0.b, c1.a, c1.b)`. No extension value is
treated as one base-field coordinate.

One attempt has the following globally shared inputs:

| Name | Source meaning | Treatment |
|---|---|---|
| `r_field_seed` | 32-byte `field_mask_entropy` | Seeded tape; not independent M31/QM31 coins without a seed-expansion hybrid |
| `r_salt_seed` | 32-byte `leaf_salt_seed` | Separate seeded tape; one derived salt is shared by the C1 and C2 leaf at the same index |
| `mask_nonce` | pre-reserved public attempt identity | Public binding, not entropy |
| `H` | one coherent hash/random-oracle cache | Shared by commitments, transcript, salts and all attempts/sessions |
| `w` | private transfer witness | Determines the semantic trace and helper offsets |

`build_mask_material_for_layout` expands `r_field_seed` sequentially into the
relation-free C1 cells, ten 1024-row mask-only M31 columns, one 1024-row QM31
`g` table and inactive-row QM31 `h1_padding`. Each applicable inactive block is
balanced by a dependent coordinate. These objects are correlated outputs of
one seed. The positive-transfer overlay discards the column-3/row-1014 draw
before overwriting that active cell; it does not restore an independent coin.

## Chronological blocks

For an affine row below, “affine” means only after fixing the named public
history and replacing the seed expander by its ideal tape. Every block retains
the same global coin identities; rows may not be checked independently.

| Block | Public observation | Conditional shape | Shared dependencies | Promotion status |
|---|---|---|---|---|
| X0 | statement, before/after state, account envelope, profile, nonce | Public/deterministic | `x`, `mask_nonce` | Inventoried; production envelope source is incomplete |
| A0 | masked 16 semantic C1 columns plus ten mask-only columns | M31 affine in ideal mask tape before hashing | semantic offset `s(w)`; relation-free cells; inactive balancing | Source-linked locally; global same-public difference basis is not proved |
| N0 | copy helper H1, G and other C2/helper tables | Mixed | A0, `g`, `h1_padding`, lambda/chi and witness trace | Unsupported nonlinear/helper coupling; blocks affine promotion |
| C1 | C1/C2 leaf bytes, shared salts and roots | Random-oracle commitment, not affine | A0, N0, `r_salt_seed`, `H` | Source serializer exists; ROM coupling/programming theorem open |
| S0 | initial claim and ten semantic/sumcheck rounds | Polynomial/nonlinear | A0, N0, transcript challenges from C1 and prior messages | Unsupported nonlinear block; a Jacobian is invalid evidence |
| P0 | point claims at transcript-derived points | Linear evaluation only after points/history are fixed | same A0/N0 coins already exposed through C1/S0 | Conditional map constructible, but no stacked global source instance |
| O0 | inactive weighted sum and two sequential OOD answer rows | Linear evaluation after samples are fixed; sampling is adaptive | A0/N0, prior transcript, distinct-sampler failures | Map and failure kernel not instantiated |
| R0 | four relation rounds and later fold roots | Polynomial relation plus linear folds after challenges | all earlier trace/helper coins, gamma/alphas, `H` | Unsupported joint nonlinear relation stage |
| F0 | final256/final coefficients | Conditional linear transform of the folded relation codeword | R0 and every earlier shared coin | Source layout known; public quotient theorem absent |
| Q0 | q22 schedule, raw C1/C2 leaves, shared salts, later leaves and authentication frontiers | Opened values are conditional linear projections; authentication is nonlinear | A0/N0/F0, transcript-derived schedule, `r_salt_seed`, `H` | Raw negative certificates exist; complete stacked image is open |
| E0 | success/failure, retry/account/publication events | Subprobability kernel | all blocks and external sinks | Deferred to R4/R5; cannot be omitted from the full view |

The fixed serialization partition remains 697 QM31 fields:
`1 + 270 + 87 + 1 + 58 + 24 + 256`. Roots, nonces, q22 opening records,
salts and frontiers are additional byte observations. The positive overlay's
`claims : [QM31;84]` is an internal relation input, not evidence that the
serialized 87 point fields have been source-corresponded. This 84/87 boundary
must be resolved by the complete generated candidate source.

## Required stacked affine statement

For any supported chronological affine cut and fixed reachable public history
`h`, the candidate gate must construct one matrix, not marginal tests:

`Y_old = a_w(x,h) + A(x,h) r`

`Y_new = b_w(x,h) + B(x,h) r`.

Its target columns must conservatively cover every valid same-public change in
`[a_w;b_w]`. The necessary source theorem is
`im([T_old;T_new]) subset im([A;B])`. No current source function constructs
`T_old/T_new`, and the duplicate-selection vector is only one mandatory
generator. Sampled witnesses, finite differences and tangent/Jacobian spans
are expressly insufficient.

## Exact blockers to R2 promotion

1. The generated positive q22 host path remains only partially reconstructible
   (7/10 transformations); three old artifact preimages are missing.
2. No universal same-public witness-difference generator theorem exists for
   A0, N0, S0, R0 or their stacked view.
3. H1/C2 construction, semantic sumcheck messages and relation messages have
   not been supplied with conditional affine laws or a nonlinear coupling.
4. No source instance expands the complete 697-QM31 view and all QM31 values
   into the exact M31 matrix rows while preserving shared coins.
5. Seed expansion, salted Merkle commitments and adaptive transcript/oracle
   programming remain explicit hybrids, not zero-cost assumptions.
6. The public quotient `c(x,h)` needed by a statement-only simulator is not
   constructed. Pairwise containment alone would not discharge R3.

Accordingly R1 closes the inventory/model boundary but blocks promotion to a
full-view gate. R2 may implement certificates only for source-supported affine
subblocks and must return `Unsupported` for the nonlinear or unauthenticated
rows above.
