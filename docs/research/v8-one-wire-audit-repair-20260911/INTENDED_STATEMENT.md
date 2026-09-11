# Frozen intended statement: V8 one-wire refinement

Audit target: `30a303a344dbb42e24ad8f42a8804819747942bc`.
Repair base: the same commit, on `research/v8-one-wire-audit-repair-20260911`.

This statement deliberately separates the literal proof body from the public
statement/context and from the causal prover strategy.  A parsed body is not a
complete payment instance: the selected relation callback receives the
ordinary functional and its claim from the outer semantic verifier, and the
payment/context checks occur outside the callback.

## Functional same-body endpoint

For one literal submitted body, public statement/context, and one source-shaped
functional execution, successful parsing and all functional verifier checks
must construct values consumed by the relation from that *same body*: 697
canonical fixed fields, roots, nonces, 22 original-ordinal records, paired
frontiers, component claims, OOD answers, inactive claim, compact responses
and final256.  Together with the independently constructed public semantic
functional/claim and legal causal prefixes, successful functional verification
must construct the corresponding ideal execution, or an explicit shared raw
hash collision/C1 late-target/C2 late-target failure.

The construction may only use data known at the relevant source boundary:
C1 before later OOD/gamma work; C2 at its post-lambda/chi boundary; response0
before alpha0; final256 before query sampling; and each later response before
its following alpha.  It must work for all continuations of a shared prefix.

## Literal-source endpoint

A successful run of the pinned Rust `relation_callback.rs::verify_relation`
and its actual outer caller must construct the functional run above, including
the same byte parser, hash-call order, mutable multiproof loop, semantic
functional/claim, public statement/context binding, and causal transcript
challenges.  This endpoint may not take the functional run, a `Program`,
`SuccessfulAt`, `idealAccepts`, `MatchingWire`, or a coherence certificate as
an unexplained input.

## Explicitly excluded conclusions

This audit-repair task does not prove a global probability bound, a
resource-bounded payment extractor, Fiat--Shamir security, full-view ZK,
complete SBF/Rust refinement, or CU parity.  In particular, no 100-bit claim
is implied by a deterministic same-body lemma.

## Present repair status

The previous headline theorem accepts an independent `Program 22` and body;
it therefore does not meet either endpoint.  The first repair leaf maps every
body-controlled relation field to a literal canonical field index and proves
that it comes from the parsed same body.  It intentionally leaves outer
semantic/context construction and causal source refinement as visible
obligations rather than hiding them in a supplied program.
