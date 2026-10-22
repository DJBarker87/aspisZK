# Row-31 materialized join specialized to SolanaDigest under P3

This focused corollary specializes the existing actual row-31 materialized conditional join to the source-derived public `SolanaDigest` wrapper model `p3PublicDigest32 sha256`. It fixes the interpretation function to `hashBytes sha256 = decodeState ∘ sha256`, hence each successful digest operation interprets as `decodeState out = decodeState (sha256 (flatten parts))`. The former generic `hdigest` premise is proved internally by the wrapper record equality and `p3_success_interpreted`.

The theorem preserves the original successful `QueriesModel.queries` call, `hstate`, literal successful run, and existential `absorbed`, exact `pairs`, decoded `blocks`/`advances`, selected state, query read, and scan result. It adds no random-oracle law, no digest regrouping axiom beyond the documented conditional P3 model, and no replacement equality assumptions. The P3/hash function remains explicit. This is conditional on the documented P3 primitive interpretation; it does not prove SHA-256 or Solana runtime behavior.

The unchanged row31 source/object, wrapper source/object, P3 interpretation source/object, generated wrapper Types, and P3 regroup source/object are pinned in `attempt/direct-import-pins.json`. The exact successful command/profile and focused receipt are retained in `attempt/`; compiled `.olean` files are intentionally not included.

Focused compile: Lean 4.32.0, exit 0, 4.525 s; peak aggregate RSS 3,421,978,624 B; peak process RSS 3,464,429,568 B; process swaps 0. Named `#print axioms actual_query_row31_solana_p3_materialized_join`: `[propext, Classical.choice, Quot.sound]`.
