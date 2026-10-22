# QueryScan finish accepted-value bridge (v1)

This packet proves that a successful `QueryScan.finish` returns exactly the accepted U32 array and that its values agree with the `accepted` list in `Query31ExplicitScanBody.q22StateOf` for the same scan state. The proof applies the retained `finish_success_iff`, then shows the `accepted_len` prefix covers the full 22-element accepted array.

The focused declaration is `AspisR1QueryFinishAcceptedBridgeV1.finish_success_accepted_values`. It compiled at source revision `549a02797cfd1c536fea9e826613c886652f59d6` with Lean 4.32.0, exit 0 in 11.886 s, peak aggregate RSS 2229354496 bytes and 0 swaps. Its axiom report is `[propext, Classical.choice, Quot.sound]`. The `.olean` is intentionally not included; its SHA-256 is `ea93804b79373a673a29c962ffe0112eaed638d84707c411ff598036ddeb25c1`.

`dependencies/closure.json` records all 3956 selected imports with no missing modules. `dependencies/direct-import-pins.json` identifies the selected direct owners. This lemma only connects `QueryScan.finish` to `q22StateOf`; it does not prove the DriverTrace-to-scan structural composition or scanner reachability.
