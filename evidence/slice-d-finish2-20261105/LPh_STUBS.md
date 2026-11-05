# NGW local-record opaque multiplication table

| Native opaque call | Paired emitted Lean theorem | Caller-established domain |
|---|---|---|
| NGW_points::product(bit,carry,log) | NGW_ProductLaw.total | SAME selected alpha coordinate and carry canonical; input array canonical; reverse-loop invariant gives canonical carry |

The native step returns an arbitrary canonical QM31 reply in a LOCAL record and logs both exact operands; it never multiplies in Kani. Under ruling (y), the Lean interpretation substitutes the unique exact emitted product, whose natural value and canonicality are proved by total, from NGM_ProbeTransport.qm_mul and AspisR1.LPi_TowerValues.qm_mul. This is P6/D188 option-A reclassification; no new trust or successful child premise. The complete statement-points packet is CLOSED; exact native pairs, canonical domain and audit are NGW_CLOSED.json.

## New factor/circle packets (CLOSED constructor composition)

| Native opaque call | Paired law | Domain derivation |
|---|---|---|
| NGW_new::product in regular row, calls0..3 | NGW_ProductLaw.total | canonical SAME a,b selected from CLOSED statement_points; NGW_FactorRow.total derives canonical ONE-a/ONE-b; exact source-order pairs (aa,bb),(a,bb),(aa,b),(a,b) |
| NGW_new::cmul in circle initialization | NGW_ProductLaw.total | SAME z[k].x/y canonical; producer is explicit NFW boundary |
| NGW_new::cmul in circle step | NGW_ProductLaw.total | SAME carried x and first double's y canonical; closed double packet and loop invariant |
| NGW_new::dbl | CLOSED NGM double packet; exact emitted FIn_WeightsExtract.double, canonicality NGW_ConstructorQM.double | SAME canonical x/y at each source-ordered call; no double success premise |
| retained NGM_helpers::scale / NGW_round::scale | AspisR1.NGM_RoundScale.total | exact claim, QUARTER=536870912; total even on raw inputs; native captures K095/K096 pass/fail; parent round remains OPEN |

The opaque polynomial reply in round is a callee-boundary oracle under (y), not a field stub or an assumed CLOSED packet: polynomial remains OPEN. No parent credit follows from it. Native factor values are arbitrary canonical replies; their interpretation is the exact natural emitted value under the named Lean laws. No field multiplication runs in Kani.

Final constructor product interpretation and caller-domain propagation are NGW_NewInterface.cohort, NGW_FactorOuter.source and NGW_CircleOuter.source (all canonical coordinates, no curve or success premise). No unpaired native field stub is admitted. Polynomial and round opaque callee replies remain OPEN boundary observations until their actual packets close.
