# R17 joint composition: explicit compatibility boundary

Date: 2026-09-20. Base `e40bab20a5db3544b2000a2549f6fcd14b93c2fc`
plus this changeset. No production protocol or staged host source changed.
This is not a full privacy theorem or a new hiding assumption.

## The previously implicit first G point

The G-only 624-row diagnostic omitted the first G point because it is
determined by the 271 mixed coordinates. It is nevertheless serialized.
When H1's semantic contribution is compensated by changing G coordinates,
preserving this point is an obligation, not a free consequence of separate
rank counts.

The new `VandermondeJoint` diagnostic explicitly retains all three G point
claims. For each of 1022 OOD-zero quotient basis directions, it checks the
first point equals the actual `mask_eval` of the retained mixed coordinates.
At both checked-in actual verifier prefixes the 625-row map has rank 601:

- 22 raw/fold compatibility equations;
- one first-G-point/semantic-coordinate terminal equation;
- one first-relation evaluation equation.

The terminal equation has coefficient one on the first G point, whereas
the raw/fold equations have no point or coin coefficients. The relation
equation has a nonzero sent-polynomial coefficient. Thus these 24 equations
are independent; the checked pivot inverse supplies the matching lower
rank. The old 624-row mode and negative regressions remain available.

## Compiled compatible-image composition

`lean/AspisV8R17/CompatibleGluing.lean` proves a general composition lemma:
choose H to match its retained view, then choose G to match its view and
the desired shared messages minus H's shared contribution. This succeeds
only if the requested observations satisfy the combined compatibility
equations, H's actual contribution satisfies its consistency law, and G
covers its **entire compatible image**. All these are explicit premises.
The reverse inclusion separately requires G's consistency law.

The lemma is about existence, not equal fiber counts or uniform conditional
distributions. Nonlinear arbitrary maps also satisfy its signature; it
therefore cannot establish a uniform posterior just from surjectivity.
No source coverage premise has been silently discharged by naming it.

The intended fixed-prefix instantiation has two shared equations, not one.
With C1/context fixed, let `r` be the 271 normalized semantic coordinates,
`p` the six compact relation coefficients, and `L(r)` the structured-mask
evaluation at the final semantic challenge point. Write

`E_alpha(p) = (1-alpha^4)*p0 + alpha*p1 + alpha^2*p2 + alpha^3*p3
              + alpha^5*p5 + alpha^6*p6`.

The shared check is `(L(r), E_alpha(p))`. For each channel its check value
is its semantic terminal contribution and
`dot(Final256, folded weights) - alpha^4 * ordinary_claim / 4`.
This is the literal omitted-c4 convention. All OOD interpolant shifts and
fixed other-column contributions must be treated as affine offsets, not
dropped. The source diagnostic uses zero-OOD difference directions.

In this candidate decomposition H1 has 347 retained raw/point/final values;
G has 348 including its inactive-sum coordinate; shared coordinates number
277. The expected compatible dimension is therefore
`347 + 348 + 277 - 22 - 22 - 2 = 926`.
This is a derived target, **not a measured joint rank or a closed source
theorem**. H1/G channel normalization by gamma powers must also be retained.

## Source-grounded H1 terminal dependence

Inspected unchanged source, identical to base
`9e432896a4e1515efebe940b71fd9b4f9f009189`:

- `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs`,
  `copy_residual` at line 339; SHA-256
  `50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5`.
- `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`,
  `composition_parts`/`terminal_parts` at lines 1216/1285; SHA-256
  `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`.

The copy residual is `a*(h*b+c)-b*p`, multiplied by the copy-active selector.
The terminal has both `mu*h` and `mu^2*(1-active)*h`. Its H1 difference is
therefore

`eta * (eq*thetaPower*active*a*b + mu + mu^2*(1-active)) * delta_h`.

`HelperAffine.lean` proves this identity over any commutative ring and
proves that each Horner lane multiplies the starting-value difference by
theta. This retains the inactive-helper term; substituting a generic
state-only terminal without that term would be incorrect. The staged G
replacement and positive-transfer correction do not use H1 in their added
terms (the positive correction uses C1 claims).

This is source-shaped algebra, not a Rust execution refinement. Fixed C1
context is explicit; a witness change still needs the earlier nonlinear
incidence offset and preservation of the relevant C1 observations.

## Verification

Lean: existing `/Users/dominic/ZK/AspisFormal` cache, smallest leaves first,
`lake env lean -j1 -M1800 -R <pack>/lean -o <cached .olean> <leaf>`.
Rust: offline/locked/release/jobs=1, explicit ignored test
`r17_actual_source_prefix_joint_ready_image`, with
`ASPIS_R17_PUBLIC_PREFIX_LOG` selecting each checked-in public audit record.
All measurements below report zero swaps.

| Target | Exit | Wall seconds | Peak RSS bytes |
| --- | ---: | ---: | ---: |
| `CompatibleGluing.lean` | 0 | 8.75 | 1258717184 |
| `HelperAffine.lean` | 0 | 8.45 | 1344978944 |
| joint-ready G, actual world0 prefix | 0 | 29.88 | 557547520 |
| joint-ready G, actual world1 prefix | 0 | 8.49 | 81182720 |

`compatible_gluing`: propext, Classical.choice, Quot.sound;
`joint_image_compatible`: no axioms;
`helperTerminal_difference`: propext, Quot.sound;
`horner_start_difference`: propext. No sorry or new axioms.
Logs under `/tmp/aspis-r15-host.drHYn9/` are
`r17-compatible-gluing-lean.log`, `r17-helper-affine-lean.log`, and
`r17-joint-ready-world0/1.log`. No unchanged full suite was replayed.

## Exact next obligation

Construct the actual H1 semantic-coordinate contribution and prove its two
consistency equations above, including the serialized first G point and
compact relation claim. Instantiate the compatible-image lemma with the
legal H1 pad map and G map, then justify equal conditional fiber counts.
The new G checks cover only two fixed source prefixes; H1 coverage at those
prefixes and the universal/adaptive exceptional-event bounds remain open.
Shared-oracle/seed/commitment, failure/retry/publication and soundness
obligations are unchanged and still necessary.
