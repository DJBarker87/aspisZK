# Literal query and rho density evidence

This bundle preserves the focused Lean evidence for two independent-answer density adapters over the literal transcript model. `LiteralQueryDensity.row31_density` bounds the query bad event at row 31 after deriving its selected set from the supplied prefix and message. `LiteralRhoDensity.row32_density` bounds the rho residual event using the prefix-derived matching data and ordered query list.

These results do not establish terminal acceptance, decoder/extractor success, D3, or a shared-oracle security conclusion.

The failed `LiteralQueryDensity-a` attempt is preserved; it emitted one axiom report containing `sorryAx` and failed on the missing `independentMean_const` lemma. `LiteralQueryDensity-b` is the final green target. `LiteralRhoDensity-a` is green. Final and direct-import object files are retained only in the deterministic archive. Source hashes, receipts, resource metadata, axioms, import pins, and runner pins are in `source-manifest.json`.
