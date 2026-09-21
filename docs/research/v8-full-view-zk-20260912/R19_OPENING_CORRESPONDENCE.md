# R19 internal-opening correspondence

This is a source audit plus compiled field algebra and actual-source differential
tests. It is **not** a machine-checked refinement of Rust words to a field.
The frozen source hashes are in `evidence/r19-opening-b/r18-stage.json`.
All names below refer to that final reconstructed stage, not an older template.

## Exact boundary

`r17_host_relation::opened_mode` retains the complete old primary block through
`verify_two_minimal_subtrees_v7_bytes`. The new branch is immediately **after**
successful paired authentication. Default host execution still calls the old
combined reference and compares its result. Only the specifically named
`all(target_os="solana",r19_no_opening_reference)` configuration bypasses that
duplicate suffix. No earlier return, decoder, denominator or hash was deleted.

The implication under review is:

> On a parser-valid input, primary success entails success of the old combined
> reference with the same line roots and the sum of the two folded values.

It is not necessary (and would be wrong) to equate the standalone reference's
error ordering with the primary. On primary failure, both the old wrapper and
new wrapper return immediately, before their behavior diverges.

## Source correspondence

| Item | Actual source binding |
|---|---|
| Fibre selection | `circle_norm::Selected::new` calls the identical `selected_circle_fiber_points_shared(20, queries)` used by `opened_values_reference`. Both enumerate `(x,y),(x,-y),(-x,-y),(-x,y)` in that order. |
| Canonical input | `query_arithmetic::gamma` decodes all 104 C1 and 48 C2 packed limbs before constructing any result. Each packed limb is bounded by P; equality to P rejects. This justifies the subsequent otherwise non-validating G accessor at helper slots 4..7. No unchecked G limb can escape the earlier validation. |
| Gamma combination | Both paths use `StateOnlySpendQueryPowers::new(p.gamma)`, the same C1 scalar coefficients and C2 helper coefficients. The primary computes S, then G as gamma^27 times helper 1, then R=S-G. The retained host assertion compares the optimized decoder/recombination to `gamma_combine_v6_packed_layer0`. |
| Chord denominator | Both compute L=a+bx+cy. Primary sign reuse is exactly the four signed fibre points. `inverse_lines` receives those denominators, the same selected circle points, base denominators 2x/2y, and t=2x²-1 built in the same loop. No external line hint is used. |
| Batch inversion | On success the norm/line implementation returns reciprocals of the identical L values and 2x/2y. Its source uses the quadratic tower norm and line identity already exercised in retained R37/R38 gates. On batch failure the primary does **not** return early: individual `try_inv` retains per-record canonical/domain ordering. Base x/y zero is checked before use. |
| Interpolants | Primary uses IR for S-G and IG for G. Reference receives `[IR[0]+IG[0], IR[1]+IG[1]]` and the same `use_x`; the choice of x/y and all signs are unchanged. |
| Fold | `quotient_fold::Prepared` expands the same normalized four-slot fold. For fixed alpha, reciprocal 2x and reciprocal 2y, this is a field-linear functional of four quotient values. It does not require honest encodings or zero image residuals. |
| Authentication | Both hash the same C1 bytes `[0,403)`, C2 bytes `[403,589)`, salt `[589,621)`, tree tags, SHA function and query IDs. Both sort entries by the same ID and call the identical paired subtree verifier with the same roots, depth 18 and frontier bytes. |
| Line roots | Both return `2*x*x-1` in original query order, independent of the subsequent sorted authentication entries. |

For each slot, with the same reciprocal d of L, field arithmetic gives

`((S-G)-IR)*d + (G-IG)*d = (S-(IR+IG))*d`.

The compiled `opening_removal_bridge` states this for arbitrary field values
(indeed an arbitrary commutative ring with a supplied common multiplier).
Weighted-contraction linearity then applies to the four-slot fold. Thus the
extra Terminal comparison agrees provided the retained arithmetic kernels
implement their documented operations. The reference's canonical, domain and
authentication checks are already implied on primary success by the bindings
above. No Fiat–Shamir or hiding premise is involved in this implication.

## Executed differential evidence

`r19_opening_check.rs` constructs 32 arbitrary authenticated packed-record sets,
not necessarily honest witness encodings. It varies full-QM31 inputs, x/y
interpolants and fold challenges. It compares the actual primary without the
suffix against the actual retained wrapper, and on success against the
standalone combined reference.

It also exercises all 3,344 packed limb positions, all 88 fibre chord poles,
all 52 root bytes, 88 payload/salt mutations, every supplied frontier node,
and all 22 query-index mutations. Combined-fault controls place a canonical
fault before/after a chord pole, exercising batch-failure fallback and the
original wrapper's error priority. The source code retains all these cases.

`opening-gate.log`: exit 0, wall 29.14 s including compilation, peak process
RSS 536,980 KiB, swaps 0. Scope limits were 5/7 GiB and zero swap. The original
R18 world-0/world-1 proof files pass the primary SBF build without changing their
bytes. The corresponding mutated-final controls reject at the diagnostic cap;
supported-budget runs exhaust and are not counted as checked rejections.

The independence of these finite tests and the Lean algebra is intentional:
neither is described as a universal machine-checked source-semantics theorem.
The source audit supplies the correspondence; retained runtime differential
tests continue to guard it.
