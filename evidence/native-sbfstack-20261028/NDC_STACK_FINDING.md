# Stack-frame finding: staged audit

Frozen source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Stage 1 established fresh hashes for all three requested artifacts, and exact
`.text` equality with retained unstripped linked outputs (NDC_I001–003).
Full symbol/instance and source/runtime analysis follows in stage 2.

34 diagnostic function families were collected from NCY_B001/B002. No
non-generic warned symbol family occurs in the linked outputs. Three other
`core::array::try_from_fn` monomorphs occur in default/devnet; their hashes
must not be confused with the diagnostic instance. No reachability or
stack-safety closure is claimed by this intermediate finding.

No shipped files, keys, runtime configuration or logical assumptions changed.
No Kani/Lean/build/VM run. Three admitted capped inspection scopes; 7 remain.
