# Final partial-context formatter audit

Seven fresh audit batches pass:12,581 structured declaration results and12,581 full raw #print axioms results, covering654 fresh selected contexts. Combined with the2687 unchanged pinned contexts audited in RPz4, this covers **3341 green contexts and103830 declaration queries**. There is no completion error, import-header mismatch, missing green context or duplicate owner/name query. Repeated global names do not establish proof-term identity.

The all-declaration standard-only gate is **FALSE**: the observed **180 formatter records use85 nonstandard axioms**, matching the inherited count. PublicPreparation.Funs contributes108 records; RecordParser.Funs and PrefixAggregateParser.Funs contribute36 each. The complete names and axiom sets are in RPz5_combined-audit.json; fresh raw outputs are RPz5_688 through694, and inherited raw results retain their RPz4 attempt references. No audited declaration outside these formatter families reaches a nonstandard axiom. These are observed existing generated definitions, not new or accepted top axioms.

**Fresh Rc10/Rc7 formatter proof-term reachability: UNKNOWN.** Both tops are blocked by the Phase-owner source conflict. Neither a cached top's historical standard axiom report nor the current partial audit substitutes for a fresh top. No claim that the85 axioms are absent from that fresh top is made.

The parser direct-reference filter retains the predecessor's limited scope; it does not establish absence of pure helper sharing for every PublicPreparation formatter family. No whole-prefix deletion or generated-file change is proposed or performed. No nonstandard axiom is added or adopted by this job.
