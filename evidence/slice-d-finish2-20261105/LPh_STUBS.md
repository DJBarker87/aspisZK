# NGW local-record opaque multiplication table

| Native opaque call | Paired emitted Lean theorem | Caller-established domain |
|---|---|---|
| NGW_points::product(bit,carry,log) | NGW_ProductLaw.total | SAME selected alpha coordinate and carry canonical; input array canonical; reverse-loop invariant gives canonical carry |

The native step returns an arbitrary canonical QM31 reply in a LOCAL record and logs both exact operands; it never multiplies in Kani. Under ruling (y), the Lean interpretation substitutes the unique exact emitted product, whose natural value and canonicality are proved by total, from NGM_ProbeTransport.qm_mul and AspisR1.LPi_TowerValues.qm_mul. This is P6/D188 option-A reclassification; no new trust or successful child premise. The table is OPEN until the theorem and native controls pass and the full statement-points packet composes.
