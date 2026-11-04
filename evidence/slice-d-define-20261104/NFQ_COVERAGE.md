# D union Q union S coverage

**581/587 rows covered; 6 outside.** No claim of exhaustive coverage beyond the canonical inventory.

Function membership matches the original VERTICAL-SLICES semantics. NFQ_COVERAGE.json provides all 587 assignments and per-transaction shortest canonical paths. TX1 entry reaches 345/345 rows; TX2 entry reaches 234/242. Eight TX2 rows lack a TX2 path. Two have slice membership through a TX1 path; six remain outside all slices. Membership does not prove TX2 reachability or native closure.

| Outside row | Function | Reason |
|---|---|---|
| TX2:008 | `crates/aspis-core/src/field.rs::CM31::write_le_bytes` | No canonical path from either transaction root; helper is an inventory-only conservative node, absent from Q/S. Reachability remains unestablished; adding it would change the defined call-cone complement. |
| TX2:024 | `crates/aspis-core/src/field.rs::QM31::write_le_bytes` | No canonical path from either transaction root; helper is an inventory-only conservative node, absent from Q/S. Reachability remains unestablished; adding it would change the defined call-cone complement. |
| TX2:029 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::c0` | No canonical path from either transaction root; helper is an inventory-only conservative node, absent from Q/S. Reachability remains unestablished; adding it would change the defined call-cone complement. |
| TX2:030 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::c1` | No canonical path from either transaction root; helper is an inventory-only conservative node, absent from Q/S. Reachability remains unestablished; adding it would change the defined call-cone complement. |
| TX2:046 | `crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31` | No canonical path from either transaction root; helper is an inventory-only conservative node, absent from Q/S. Reachability remains unestablished; adding it would change the defined call-cone complement. |
| TX2:211 | `programs/r1-cost-probe/src/lib.rs::error` | Canonical graph omits map_err(error) callback edge. Frozen first_decoded calls map_err(error); callback is not a direct-call target in the inventory. |

Frozen `first_decoded` ends in `.map_err(error)`, but canonical_callees lists only tx1 and observer. This is an inventory callback omission. Add a separately reviewed callback edge in the authoritative inventory to cover error; this job does not modify that inventory. Covered rows lacking a TX2 path are listed below.

- TX2:018: `crates/aspis-core/src/field.rs::QM31::from_cm31`
- TX2:037: `crates/aspis-core/src/field/wide_exact.rs::WideExact::new`
