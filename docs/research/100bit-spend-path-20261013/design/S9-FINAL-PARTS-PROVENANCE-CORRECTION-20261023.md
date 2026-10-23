# Final-parts provenance: reporting correction and repair

The historical “own final parts” wording for the untraced Parent/Pair-kappa/source-kappa endpoints is stronger than the provenance exposed by their theorem statements. This includes `S9Tx2CurrentKappaEndpointV1.source_tx2_current_returns_native_kappa_polynomial`. The accepted proof internally chooses the vector reached by the actual source phase execution, but the exported conclusion only supplies a canonical vector and its kappa-polynomial equation. It does not export an execution trace relating that same existential vector to the actual final parts writes.

Historical evidence: [source endpoint packet](../evidence/s9-tx2-current-native-kappa-endpoint-v1-20261023/manifest.json), manifest SHA256 `244988611e4939ac16cda28616a7e91b20472578a05e54a6d2408d69f5a9620e`; exact checked source `73913eee44bd0b208a58f7e0cc1cd06b4345a7a09cb8932e14805d971ecf7835`. Its original source/comments/receipts are retained unchanged. This note supersedes any interpretation of “own parts” in that packet as an exported operational-provenance guarantee.

The exposed result has the shape `∃ parts, Good parts ∧ Can out ∧ decode out = kappaPolynomial parts kappa`. It does **not** expose `FinalPartsTrace ... parts ...`. Consequently, a consumer cannot attach separately proved spend-relation meanings to that existential vector, nor identify it with another theorem's existential vector. The compared source endpoint's structural equalities and transfer to the round claim do not by themselves repair this missing vector provenance.

The source-binding work remains valid: the same source-created View and proof range, original resume, constructor and Pair calls, strict-reader/constructor canonicality, exact span, source output map, round calls and comparator/dot events are preserved. The correction concerns what the exported polynomial-vector interface allows downstream proofs to compose. It does not invalidate those source-call or arithmetic proofs.

The required replacement is an endpoint returning the **same** vector together with pure actual source phase events (`FinalPartsTrace`), its canonicality, and its kappa equation. Relation meanings must then consume those actual calls and writes. The lead owns this trace/provenance strengthening; it is pending at the time of this note. A trace structure must contain actual events, not the desired relation as a hidden premise.

There is no protocol, Rust, artifact, compute-budget, security metric or adversary change. No accepted proof has been rerun or silently promoted. The goal remains at least100-bit per-attempt soundness without grinding credit. The target is not yet established; actual final-parts relation interpretation and the other documented implementation/security obligations remain open.


## Exact extent and replacement interface

This correction also applies to the “own/final parts” operational interpretation
of the shared/unshared parent canonicality endpoints, both branch polynomial
endpoints, `S9ActualPairKappaPolynomialV1.actual_pair_returns_own_kappa_polynomial`,
and `S9Tx2ComparedKappaEndpointV1.source_tx2_compared_claim_is_own_kappa_polynomial`.
Their checked statements and receipts remain unchanged. They expose existential
canonical arrays and equations, not a public predicate relating that same array
to the implementation's actual phase writes. Even the parent endpoints' final
sum-call witness does not expose the chain producing its input array.

An existential polynomial vector alone does not establish implementation
component semantics: a constant-coefficient vector can encode an already
canonical output. Consumers must not identify such a vector with another
existential vector or attach separately proved relation contributions to it.
The concrete final-sum theorem whose parts array is an explicit input remains
valid and useful, as do the full shared/unshared source SSA traces that expose
the actual array updates.

The replacement public statement is:

```
∃ parts k,
  FinalPartsSourceTrace self alpha f kappa out parts k ∧
  Good parts ∧ Can out ∧ decode out = kappaPolynomial parts kappa
```

`FinalPartsSourceTrace` contains the actual source parent, branch, input reads,
powers, regular/common/partial/high/low/inactive/private/active phase calls,
threaded arrays and writes, and final sum-call events. It contains no desired
canonicality, kappa equation or spend-relation meaning. The same exported
`parts` and `k` are parameters of those events. The accepted Pair derives the
trace; canonicality and the polynomial equation are then proved for those
same parameters using the already checked phase and final-sum proofs. The
caller endpoint must retain this trace with its same native output and source
round claim. Spend-relation interpretations must consume its concrete events.

At this correction checkpoint the three focused replacement sources are
candidates: source trace, trace-to-canonicality, and traced kappa equation.
They will be checked in that dependency order. No complete source-component,
spend-relation or 100-bit claim follows from the untraced endpoint.

This is a correction to reporting and the exported proof interface. It does
not change the protocol, implementation, proof format, artifact, CU allowance,
adversary, security contract or 100-bit release target.
