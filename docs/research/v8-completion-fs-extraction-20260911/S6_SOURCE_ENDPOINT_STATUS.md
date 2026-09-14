# S6 source-endpoint status

S6 does not close `selected_root_fresh_ordinary_bad_bound`.  The failure is a
source-producer gap, not an uncompiled degree/counting lemma.

The source-static terminal audit passes at the pinned checkout:

```text
performance_verifier.rs SHA-256:
bf8a24c42c0d5493d2259fa19a70b1a8bf4ba168f661b71cfed6d33c70eebfbc
pair_forest_semantic_terminal.rs SHA-256:
efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58
```

It establishes only that the direct `payment_terminal` source body does not
lexically invoke the *shared SHA transcript* API.  Therefore the S6
guard-relaxation direction is appropriate for a later source-faithful model:
an accepted source run can pass through the same dynamic semantic computation
and omit the final terminal equality rejection for a one-way upper bound.

However, the exact current Lean configuration cannot instantiate that model.
`FSV8S5SelectedVerifierCallbacks.selectedConfiguration` installs
`readOnlyFirst` and `readOnlySecond`, both `Script ... Unit 0 := .done ()`.
The actual selected Rust path parses and consumes OOD body answers; those
callbacks are a source-shaped placeholder, not a producer for the live OOD
values, roots, or commitment checks.  The constructor also takes a caller
supplied base `Configuration`, including `z`, cuts, digest and the adversary
machine.  Consequently it does not construct one native root from the actual
selected parser/source invocation.

The existing source-cap theorem has the same essential boundary:
`actual_alpha_prefix_records_le_full256MachineFreshCap` requires
`priorSourceBound`, `adversaryFuelBound` and `workBudgetBound` as arguments.
S5 proves the numeral `420`, while the dynamic semantic script's conservative
syntax allowance is `1800`; no checked theorem derives the former source-call
bound from the selected execution.  Thus neither 420 nor the prior list bound
may be used as a completed fresh-occurrence/capacity producer.

This blocks Tickets A--D in dependency order:

1. Construct a literal selected `Configuration` from the parsed body, public
   context and dynamic transcript state, with source OOD answer callbacks.
2. Prove its `wholeStagedScript` is the selected pre-alpha Rust/source path
   through the actual alpha call, retaining the persistent oracle/cache.
3. Derive the 420-prefix call bound (or a revised bounded allocation) from
   that script, including all failures.
4. Build the pre-alpha compact polynomial and early reference family at that
   literal cut; only then prove actual bad-event inclusion in the killed
   sampler target.

The generic S6 killed-sampler, guard and finite-envelope lemmas are checked
and retained, but they are deliberately not counted as any of these source
producers.  Cached verifier outputs and usable-node restoration remain open:
without the same-root source construction, an earliest cached creator cannot
be supplied with a correctly fixed polynomial target.
