# Owned runner/validation changes

Empty RUSTFLAGS from K001 replaced by --cfg NJP_good_argument; no semantic credit for K001. NJP_run preserves the canonical timeout-text rejection and admission JSON allowed:true AND exit0 policy, with 70 Kani/80 Lean-link-audit limits. Shared launcher/reservation/shims remain unchanged.

Every Kani scope already ran the inherited strict frozen active package/edge graph gate, and actual-target package/feature metadata before execution, with the unchanged lock after it. The final native cut stage additionally checks actual-target edges against the same frozen lock and pins each inherited stage/payload/manifest/supplement input by its committed SHA256. This only strengthens validation. NJP flags occur in no frozen manifest, so earlier actual-target requests have the same dependency edges as their canonical frozen graph; no cfg-if/libc or other drifted crate was admitted. All source overlays remain private and exactly pinned.

Final-stage include source is committed and added to each scratch patch/receipt; no validation input excluded. Local Node/copy/loop support uses its own NJP prefix. Two concurrent scopes are used only under the JOB-specific allowance (one serial Kani queue and one focused Lean queue); shared infrastructure is not changed.
