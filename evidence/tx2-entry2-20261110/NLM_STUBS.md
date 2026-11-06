# Native initializer and contract calibration

No field multiplication is reached or stubbed by these harnesses. No frozen
callee is replaced by a contract. `havoc_bytes` is a scratch, weak initializer
used to generate a pre-state; it returns zero and permits modification of its
borrowed array. Its real body returns zero without modifying it. Composition
uses option A's existing P6/D188 contract semantic transport, not new trust or
trust removal.

| Interface / obligation | Receipt | Verdict / admission |
| --- | --- | --- |
| mutable slice seed contract | K009 / K010 | pass / inverted ensures fails |
| mutable slice effect contract | K011 / K012 | pass / inverted ensures fails |
| mutable slice body / unimplied caller | K013 / K014 | real body passes; caller compiler ICE; NOT admitted |
| borrowed `[u8;58295]` seed | K015 / K016 | pass / inverted ensures fails |
| borrowed `[u8;58295]` effect | K017 / K018 | pass / inverted ensures fails |
| borrowed `[u8;58295]` body / unimplied caller | K019 / K020 | real body passes / stub caller assertion fails |
| borrowed `[u8;58295]` modifies violation | K021 | violation detected |
| subarray frame | K022 | CBMC crashed; NOT admitted |

K015-K021 supply the ruling (t) controls for this exact fixed-array shape.
The claimed domain is a safe mutable borrow of the entire 58295-byte initialized
allocation, obtained with `try_into`, not a fabricated pointer or a claim about
an arbitrary-capacity Vec. Whole-allocation frame K023/K024 passes/fails as required; nonconstant-state control K025 fails as required. Every eventual caller credit needs its matched control and exact
KMX configuration. The retired slice/subarray shapes are not renamed passes.

K005/K006 are a restricted pre-state owned-data getter pair (zero bytes except
one selected arbitrary byte). They do not justify arbitrary-buffer credit.
All native claims are local support, not the five complete parameterized folds. See NLM_NATIVE_DOMAIN_FINDINGS.json: fixed capacity, restricted constructor partitions and local footprints are not silently generalized to every caller. K026/K029/K041 timeouts give no credit; K043/K044 only calibrate one local canonical KMX iteration.
