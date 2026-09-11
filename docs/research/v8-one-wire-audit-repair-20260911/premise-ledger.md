# Premise ledger

The old headline theorem takes `p : Program 22` independently of `body`.
`SuccessfulMerkleRun` constructs the parsed Wire, records and frontiers, and
`rootBound` connects only roots. `p` still supplies bodies, OOD data, weights,
claims, inactive function and causal strategy. `PathChecks`, inverse and
terminal remain caller-provided source-success conditions.

`OneWireConsumedFields.fixedAt_decoded` is different: it takes only a parsed
same body and a literal index, and proves canonical decoding of that body's
field. Its specialised projections cover claims, inactive, both OOD vectors,
all responses and final256. It has no Program, acceptance, extractor or
payment-witness premise.
