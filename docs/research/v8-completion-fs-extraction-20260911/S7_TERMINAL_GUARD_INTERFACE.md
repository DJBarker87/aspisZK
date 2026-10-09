# S7 selected-terminal guard interface

Status: **OPEN SOURCE REFINEMENT; GUARD-RELAXED MODEL ONLY**.

Base inspected: `9f161d6ba1c34adb93ab8ed0b95d26c1fac95db3`.

This note fixes the exact interface needed to turn the S7 dynamic root into a
one-way upper bound for accepted selected-source runs.  It deliberately adds
no generic callback theorem: without the literal evaluator and its source
simulation, such a theorem would only move the missing premise into a
function argument.

## Actual selected source cut

For the positive-transfer completion profile, the selected Rust order is:

1. `verify` canonically parses `body`, `public`, and `transition`;
2. `semantic` creates a transcript at the zero digest, absorbs the
   positive-transfer descriptor, profile, binding and C1 root, and samples
   the semantic challenges and ten round points;
3. the 84 claims are projected as
   `w.v[271 + (i / 28) * 29 + i % 28]`;
4. `payment_terminal` calls
   `evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1`
   and adds `positive_transfer::terminal_delta`;
5. `semantic` rejects unless that returned value equals `s.claim`;
6. only then does the structured ordinary suffix absorb the 87-field
   point-claim slice and continue.

The direct terminal call receives immutable inputs and the inspected path has
no call to the shared transcript/hash API.  The pinned source hashes are:

```text
performance_verifier.rs:
bf8a24c42c0d5493d2259fa19a70b1a8bf4ba168f661b71cfed6d33c70eebfbc
pair_forest_semantic_terminal.rs:
efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58
```

This is source-static evidence of the intended cut, not an effect/refinement
proof.

## Exact endpoint required

Let `literalRun` be an independently defined operational execution of the
pinned selected Rust entry point on one `(body, binding, publicBytes,
transitionBytes)` and initial persistent oracle.  Let `relaxedRun` be
`FSV8S7DynamicSelectedRoot.selectedVerifierScript binding body` on that same
oracle.

The required one-way theorem is:

```text
literalRun = accepted sourceResult
---------------------------------------------------------------
exists relaxedResult,
  relaxedRun = accepted relaxedResult
  and relaxedResult.semantic is the semantic state of sourceResult
  and the body, parsed fields, C1/C2 roots, z, digest and point-claim bytes
      are the values consumed by literalRun
  and the oracle state immediately before the ordinary suffix is identical
      in both runs
```

The conclusion is intentionally one-way.  Removing the terminal equality
guard admits additional relaxed runs.  It must not assert payment validity,
callback correctness, or equality of the selected terminal with a recovery
table merely to establish the inclusion.

## What is already constructed

| Interface value | Existing producer | Status |
|---|---|---|
| canonical proof fields and roots | `SameBodySemanticWire.parse` inside `FSLiveSemanticPrefix.semanticScript` | functional same-body producer; literal Rust parser refinement remains open |
| dynamic semantic challenges, `z`, carried claim and digest | `FSLiveSemanticPrefix.Success` | constructed by the functional transcript |
| exact 84-claim indexing | `FSLiveSemanticTerminalInput.ofRun_claims_eq_terminalProjection` | Lean-checked same-body projection |
| label-49 87-field absorb and suffix | `FSV8S4VerifierOnlySuffix.selectedSuffixBeforePoints` | constructed from the same body and functional digest |
| dynamic guard-relaxed root | `FSV8S7DynamicSelectedRoot.verifierScript` | functional model only |
| source callback algebra after component values are supplied | `SelectedSourceSemanticPoseidonCallbackComposition` | algebraic assembly; not literal evaluator refinement |

## Missing producers preventing the endpoint

1. **Literal public/context decoding.**  The dynamic root currently contains
   `binding` and `body`, but not the actual `public` and `transition` byte
   inputs or their canonical Rust decoders.  Consequently it cannot execute
   the selected payment terminal.
2. **Literal terminal evaluator.**  No Lean definition consumes
   `FSLiveSemanticTerminalInput.Input`, the decoded public/transition values,
   the selected helper/H/G and mask evaluators, and the positive-transfer
   delta with the pinned Rust failure behaviour.
3. **Rust-to-functional semantic simulation.**  There is no theorem that an
   accepted execution of the pinned `semantic` function produces the same
   parser result, challenges, `z`, carried claim and digest as
   `semanticScript` on the shared persistent oracle.
4. **Terminal effect simulation.**  Lexical absence of transcript calls does
   not prove in the chosen execution semantics that the terminal preserves
   the oracle/digest and returns normally.  This should follow from the
   literal evaluator/refinement, not from a caller-supplied `callbackExact`.
5. **Selected profile refinement.**  `v8_positive_transfer` is an opt-in
   research profile and `v8_structured` selects the post-semantic suffix.
   The operational simulation must pin those flags and must not inherit an
   unflagged production/default-source theorem.

`SameBodySelectedSemanticSource.source_execution_constructs_selected_bindings`
does not discharge these items: it assumes both a successful caller-supplied
callback run and `callbackExact`.  It remains a valid conditional consumer,
not the source producer required here.

## Smallest honest next implementation

Define a first-party functional `SelectedPrivateTransferTerminalInput` which
contains the canonical decoded public and transition structures plus
`FSLiveSemanticTerminalInput.Input`.  Implement the complete selected
private-transfer terminal expression, including helper/H/G, selected mask and
positive-transfer delta, as a total `Except` computation.  Differentially
test its byte/field result and every error branch against the pinned Rust.
Then prove the Rust semantic call simulates this computation and preserves the
shared oracle state.  Only at that point should the accepted-source to
guard-relaxed inclusion theorem be promoted.

Until that producer exists, S7 Wave A is correctly described as a dependent
**guard-relaxed functional root**, not a literal accepted-source root, and the
ordinary bad-event probability theorem cannot use literal verifier acceptance
as its antecedent.
