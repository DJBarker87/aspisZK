# Literal query/rho support and semantic prefix checkpoint

Base: `5dba4e4266ec6eebceb9adf49d60db5e5695bed3`.

The checked query and rho event identities now consume the same literal matching data. `LiteralQueryRhoSupport.large_support` combines absence of the two final classifier events with the first-fold equations at the 22 decoded queries and the rho-batched residual equation. It proves at least 9,558 matching positions. `MatchingSupport.large_matching_implies_claims` is the existing consumer of this threshold, together with its `Good` and `AcceptedPairing` premises. This checkpoint does not infer those equations from source execution or verifier acceptance.

`LiteralSemanticTake.read_take` and `LiteralSemanticIndex.read_index` reuse the strict semantic reader. They establish prefix stability and the exact parsed message/ordinary challenge at each successful input index. They prepare the connection to the existing 25-row semantic no-hit theorem; that event/context connection is still in progress.

Six focused targets passed on the NUC. Each final axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`; all used the 4 GiB/6 GiB cgroup limits with swap disabled. Peak RSS was below 3.5 GiB. The six targets took 1.46–2.62 seconds each. The root audit pins current source bytes, receipt/log pairs and archived objects in `evidence/j1-query-semantic-lead-review-20261015.json`. Failed development attempts remain in the bundles and are not counted as successful audits. No unchanged runtime or full-manifest suite was repeated.

A subsequent direct claims-composition target passed on the NUC but its evidence has not yet been retrieved because SSH became unavailable. It is deliberately outside this checkpoint. The incoming `98c316524` / `7c5ca8699` review branch is also outside this checkpoint and is being reviewed separately; its lifecycle rejection needs a provisioning resolution before release.

D3, decoder injection and the shared-oracle collision bound, current Rust refinement, commitment recovery, efficient knowledge extraction and the complete privacy argument remain open. The measured two-transaction path remains an engineering result, not a completed 100-bit private-spend theorem.
