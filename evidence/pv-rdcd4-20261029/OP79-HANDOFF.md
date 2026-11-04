# Runjoin step (4): op79 source/Result association

Consume `R1Z.PV_RDCD4_V201.source_reference`, importing
`R1Z.PV_RDCD4_V201` from the recorded coherent RDCD4 closure.

The theorem has exactly the original CodeField parameter, array of 1024
field elements, Point input and complete Result equality:

```lean
PV_RDCD4_V201.value inst q p = PV_CB_OwnedEncoder.owned.encoder inst q p
```

At `prover.rs:354`, specialize `inst` to the deployed WideExact selection.
The source association and its hashes are in
[v201-proof-association.json](v201-proof-association.json); the record-by-record
reachability dispositions and body bindings are in
[v201-source-bindings.json](v201-source-bindings.json). All 145 conservative
records are dispositioned: 72 historical, 11 reached, 52 typed alternatives,
10 guarded alternatives. Eleven generated named applications bind the new
reached records; source-only handwritten models receive no b3p6-1 credit.

This closes the V201 source/Result law. It does not construct Runjoin's native
producer, source-world carrier or physical/error-prefix observation. V370 and
pending D381/D386 remain the source-to-code boundary, with E1/E2 and the other
native obligations retained. The endpoint's T and premises are unchanged.

Final audit, focused replay, frozen manifest and source/object coherence
receipts are indexed by [REPORT.md](REPORT.md) and [RUNS.json](RUNS.json).
