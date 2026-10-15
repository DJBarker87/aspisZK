# Per-attempt row and density inventory

This source inventory records the two-fold unified 33-row challenge schedule and the numerical density APIs available in the Lean sources. The row map was corrected against the current Rust sources at worktree HEAD `ce1fb7255213f5b390048d1ca709fea99176ae62`. No Lean builds were run for this inventory. It does not construct the 33-row classifier or assert that any listed predicate is the concrete verifier's classifier.

## Corrected challenge-row map

There is no semantic-index shift. Rust `r1_wire::begin` draws lambda, chi, theta, zc[0..10], mu, eta at rows 0..14. Rust `r1_semantic::verify_observed` draws alpha[0..10] at rows 15..24 and circle points z0/z1 at rows 25/26. Rust `verifier::Prepared::new` draws gamma, kappa, alpha0, alpha1 at rows 27..30, then on the two-fold path the query at 31 and rho at 32. The row-0 absorb contains C1 and also supplies the lambda draw: it is not a C1-only row followed by shifted semantic rows. The one-fold branch instead places query/rho at 30/31.

| Unified row | Rust value / event | Unified sampler law | Existing numerical API (conditional, not yet classifier-composed) |
|---:|---|---|---|
| 0 | lambda; initial absorb includes C1 | `UnifiedInitialLaw.sampler_law`; `InitialSamplerLaw.own_law` (`InitialSamplerLaw.lean:28-43`), output `(c1,(p.σ 0 b,x))` for two independent answers | `SemanticBudget.roots 0 = 217600`, hence old semantic term `217600*atom`; no proof here that the current row-0 classifier depends only on lambda or is the old semantic predicate. The additional answer `x` remains part of the initial law. |
| 1 | chi | `UnifiedSemanticLaw.background_sampler_law`; ordinary row | `SemanticBudget.roots 1 = 54400`, times `atom`; current fixed-prefix classifier containment not proved. |
| 2 | theta | `UnifiedSemanticLaw.background_sampler_law`; ordinary row | coefficient 2800 times `atom`; current classifier containment not proved. |
| 3–12 | zc[0..10] | `UnifiedSemanticLaw.background_sampler_law`; ordinary rows | coefficient 100 each times `atom`; current classifier containment not proved. |
| 13 | mu | `UnifiedSemanticLaw.background_sampler_law`; ordinary row | coefficient 200 times `atom`; current classifier containment not proved. |
| 14 | eta | `UnifiedSemanticLaw.background_sampler_law`; ordinary row | coefficient 100 times `atom`; current classifier containment not proved. |
| 15–24 | alpha[0..10] | `UnifiedSemanticLaw.background_sampler_law`; ordinary rows | coefficient 2700 each times `atom`; current classifier containment not proved. `SemanticBudget.budget_sum` sums rows 0–24 to `303100*atom`. |
| 25 | z0, circle First | `UnifiedSemanticLaw.background_sampler_law`; ordinary sampler row | Old `circle_row25_D2` gives `2/P^4` under its own sampler-identity premise. Current Rust row/sample identity and classifier mapping are not proved here. |
| 26 | z1, circle Second; reseed state answer follows | `UnifiedReseedLaw.background_sampler_law`; `ReseedSamplerLaw.background_law` (`ReseedSamplerLaw.lean:26-56`), output contains `(p.σ 26 b,y)` | Old `circle_row26_D2` gives `2/P^4` under the old circle sampler identity and prior z0 exclusion. Row 26 is z1, not gamma; the extra `y` seeds the following opening state. Current classifier mapping is not proved. |
| 27 | gamma | `UnifiedOpeningLaw.background_sampler_law`; ordinary row | `OpeningSamplerBound.gamma_mass_le`: `336869026622539*gammaAtom`, for `ConcreteBinding.gammaBad W F Y`. Requires identity to the zero-excluding gamma sampler and fixed data at the prefix. |
| 28 | kappa | `UnifiedOpeningLaw.background_sampler_law`; ordinary row | `OpeningSamplerBound.kappa_mass_le`: `600*atom`; theorem parameters include fixed `W,F,F0,Y,c0,gamma`. |
| 29 | alpha0 | `UnifiedOpeningLaw.background_sampler_law`; ordinary row | `OpeningSamplerBound.first_mass_le`: `9396508281846*atom`, assuming degree ≤6 and fixed `W,gamma,w,p0`. |
| 30 | alpha1 | `UnifiedOpeningLaw.background_sampler_law`; ordinary row | `OpeningSamplerBound.second_mass_le`: `9396508281846*atom`, assuming degree ≤6 and fixed `W,V,gamma,alpha0,w,p1`. `OpeningSamplerBound.openingCap` sums the four opening terms and proves it `<2^-199`. |
| 31 | query (two-fold path) | `UnifiedQueryLaw.background_sampler_law`; `QuerySamplerBridge.sampler` | `SpendFailureSupport.matchingSet_q22_successful_containment_bound` reuses `R0C.V3.Q22.q22_bound`: `Nat.choose 9557 22 / Nat.choose 262144 22`, under all `SpendFailureSupport` premises (typed/context/matching facts, Good/AcceptedPairing, checks, outside condition, and no committed spend candidate). |
| 32 | rho (two-fold path) | `JointUnifiedLaw.background_sampler_law`; `JointNextLaw.background_law` | `JointRhoBound.continuation_rho_bound`: `21*((2^256/P^4+1):ℚ)/2^256 < 2^-119` for its 21-element `rhoBad` set. Requires `hsigma`, fixed residual data/query list from the prefix, and the completed-prefix continuation. |

The old `SemanticBudget.roots` coefficients in row order are `[217600, 54400, 2800, 100×10, 200, 100, 2700×10]`, summing to 303100 over exactly indices 0–24. The two old circle values occupy 25/26, the four opening values 27–30, and query 31. Current two-fold row 32 is terminal rho. Thus the old/new challenge *indices* align through query; the initial and reseeded sampler laws have different hash-chain/state-answer structure, and current rho adds the terminal row.

## What the count does and does not establish

There are exactly 33 challenge indices in this two-fold schedule: 25 semantic values (0–24), two circle values (25–26), four opening values (27–30), query (31), and rho (32). `UnifiedDecoderBound.decoded_bound` composes laws only after an explicit uniform fixed-prefix bound for every `i < 33`; it supplies no numerical bound.

The row partition accounts for all 33 indices, but it does not assemble 33 classifier implications. Row 0 has a two-answer initial law, and row 26 has a two-answer reseed law. The root's joint-list route fixes F/Y before gamma and may make the circle rows contribute no soundness event; that classifier theorem remains unproved here. The separate 25-row semantic total, old circle bounds, four opening-family cap, Q22 term, and rho term have different predicates and premises. This inventory does not claim that every term is applicable to a concrete row or that either special row has zero D2 cost.

For the older masked APIs, `combinedD2BudgetZ` (`R0P/MaskD2.lean:149-155`) assigns semantic indices 0–24, circles 25–26, openings 27–30, and query 31. `combinedProtocolZ_D2` (`R0P/MaskD2Instance.lean:14-47`) needs explicit sampler identities (`semChal`, `circleSample0/1`, and four `DQ.σQ` identities). Index alignment does not prove those identities or classifier containment for the unified initial/reseeded samplers.

## Circle fallback facts

The old `R0P.SemSource.circleSampleParameterWith` is total: it uses `outside_has_denominator` when the parameter has nonzero imaginary part and returns an explicit fallback otherwise (`R0P/CircleSampler.lean:173-180`). Its two fallback parameters are `(0,1)` and `(1,1)` (`:129-145`), with distinct non-rational points (`:147-171`). The first bad fiber has size at most one; the second has size at most one given exclusion of the second fallback (`:232-264`). `circleSample0_mass` and `circleSample1_mass` (`:297-329`) bound standalone events by `(1+deltaQ)/P^4`; masked D2 wrappers use `2/P^4` (`MaskD2Glue.lean:127-143,163-191`). Current Rust `circle_sample` also totalizes `secure_ood_circle_point_from_parameter` with distinct First/Second fallbacks (`crates/aspis-r1-cost-probe/src/sampler.rs:94-101`). These old Lean bounds do not identify the current row classifier or prove current Rust fallback correspondence.

## Source pins

All Lean paths below are pinned by SHA-256. Rust files are the current cost-probe sources whose row use is cited above.

| Source | SHA-256 |
|---|---|
| `lean/UnifiedSampler.lean` | `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad` |
| `lean/UnifiedDecoderBound.lean` | `a909cbb8259c00b839f13f8248f7fd8b2c6411647c97ff936f0c57145d235c3e` |
| `lean/UnifiedInitialLaw.lean` | `fdd839ffdcd0ef694abca3095ee39023f8ee18632a907cfa0bc1b379b4f70d69` |
| `lean/UnifiedSemanticLaw.lean` | `8fdadeea8dbed157df193c5037124ca5dc7223d954d271d1b859078273695543` |
| `lean/UnifiedReseedLaw.lean` | `590267c892ef9a80a92cf86948d73704427d14e45b9b20aa0a64cff5b5dedfec` |
| `lean/UnifiedOpeningLaw.lean` | `4217b0e29cf5fa111f091acedc63f3b16c3b28243b7cb074512b574e98021358` |
| `lean/UnifiedQueryLaw.lean` | `0a4e7407d442206d18174fb22f839329b067782b6e3c1e722153b150d021ddec` |
| `lean/JointUnifiedLaw.lean` | `4f47cee92e8fee6bb1b48b16a1c2000719e7e4982f41e463d7527d1ef293f623` |
| `lean/OpeningSamplerBound.lean` | `99c1f224de2c37fb5eabcc0e85f8ac37a9eccd7144d3606dfc2807ce07e82bb4` |
| `lean/QueryRhoBound.lean` | `b0a8830b0bb1b16902708682fdd7e2bec7b20ac93c4e3ec254ffb8948d89f4b2` |
| `lean/RhoSamplerBound.lean` | `67ff6adaaba17a523c7e138faf525e299d389d42cbf2dbf826de4c548eb27fa2` |
| `lean/SemanticBudget.lean` | `9662af8fef91a423fcbd2fce7b973e005be80c79e5d4031831f66e18d0cfab1f` |
| `lean/InitialResponses.lean` | `5a67cc4cb4db77f04e9f8f0d53c2d8ac1650f4fc01b130073c790bee89f3fd8d` |
| `R0P/MaskD2.lean` | `22af138da175023e657cd78ca98c15468b7c29ca166d5d14e3d02abb687e1041` |
| `R0P/MaskD2Glue.lean` | `c0d9044c08be9cd252224ebc460dbca98898bc22747702ea5ca52d2983b5f910` |
| `R0P/CircleSampler.lean` | `00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100` |
| `R0P/SemD3Glue.lean` | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/sampler.rs` | `be426dfc4049682ef2d90940ee42bf9cffbec2db1d2d9b965e9c14e491948b8c` |
