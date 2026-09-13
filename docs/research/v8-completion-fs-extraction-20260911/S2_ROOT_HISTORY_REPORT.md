# S2 root-history bridge and fresh-output slice status

Date: 2026-09-13

Base reviewed: `fb79364efa63226e97cda8010859a161436c0492`

## Checked endpoint: same root, exact alpha label

The primary S2 source theorem is now kernel-checked:

```lean
returned_root_positional_query_has_exact_alpha_label
```

For an `ExactRootFunctionalRun` and a positional decomposition of its actual
returned verifier fresh-query list,

```text
prior ++ (input, answer) :: later,
```

the theorem constructs, from that same root:

1. the actual projected root-record prefix and its literal fresh record;
2. the exact native verifier request state and its cached-inclusive history;
3. exact request/final history cuts and fresh-answer enumerations; and
4. equality between the alpha label generated at the root position and
   `relationAlphaPreferredSlotFromHistory 0 requestState.history input`.

The proof executes the native scheduler and the erased alpha machine on the
same answer prefix.  It does not reconstruct a history from fresh answers and
does not add a root-history equality, a source-alignment certificate, a
preconstructed labelled trace, target locality, event inclusion, or a
probability bound as a premise.  Thus cached records remain part of the state
on both sides of the equality.

The direct supporting leaves are:

| Leaf | Declaration | Result |
|---|---|---|
| `FSV8AlphaPrefixErasureBridge.lean` | `alpha_state_after_answers_eq_erased_native_prefix`; `alpha_seek_after_answers_eq_erased_native_request` | PASS |
| `FSV8AlphaLabeledPrefixDecomposition.lean` | `machine_labeled_answers_at_cut` | PASS |
| `FSV8RootPositionalAlphaLabel.lean` | `returned_root_positional_query_has_exact_alpha_label` | PASS |

The previously checked `FSV8AlphaExactRequestLabel` is used only after the
request has been constructed by the same root; it supplies the local
request-to-label equality.

## Checks

The S2 handoff manifest verified, the 17 selected source pins matched the
then-current base, and its finite/reference suite passed 49/49 tests.  The
finite tests cover reduced history/sampler/router models; they are not an
Aspis source refinement or random-oracle proof.

The missing dependency artifact
`FSV8AlphaRootLabeledTraceConstructor.olean` was rebuilt as one focused
predecessor, using the pinned Lean 4.32 cache.  No package-wide build ran.
Every focused NUC run used a systemd scope with `MemoryHigh=7500M`,
`MemoryMax=8G`, and `MemorySwapMax=0`.

| Target | Exit | Wall | Peak RSS | Swap | Axiom output |
|---|---:|---:|---:|---:|---|
| `FSV8AlphaRootLabeledTraceConstructor.lean` | 0 | 2.82 s | 6,849,076 KiB | 0 | standard foundations |
| `FSV8AlphaPrefixErasureBridge.lean` | 0 | 2.75 s | 6,835,732 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8AlphaLabeledPrefixDecomposition.lean` | 0 | 2.84 s | 6,847,572 KiB | 0 | none |
| `FSV8RootPositionalAlphaLabel.lean` | 0 | 2.83 s | 6,809,640 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

The first root-theorem elaboration exposed only two local draft defects: a
record-answer projection needed an explicit simplification, and two ambiguous
`.machineFresh` constructors needed the `UnifiedExposureRecord` qualifier.
They were repaired without changing the theorem statement.  The final run
has no warnings, `sorry`, `admit`, custom axiom, or `native_decide`.

## S2 endpoints not constructed

The source-labelled prefix and routed-output consumer are **not** promoted by
this update.  The following missing source producers are precise, substantive
boundaries rather than probability terms:

| Required producer | Status | Reason |
|---|---|---|
| Selected V8 work-script grammar/no earlier alpha marker | OPEN | `Configuration.firstWork` and `secondWork` are arbitrary scripts.  A documented two-query counterexample can consume/reuse slot zero while satisfying `n+m <= 108`. |
| Selected `adversaryFuel <= q1`, `n+m <= 108`, and literal alpha-prefix bound | OPEN | `Configuration` exposes arbitrary fields; `FSV8ActualRootSourceFreshCap` takes all three as premises. |
| Same actual accepted root to local V7 aligned history before projection | OPEN | The local bridge retains only `map projectRecord` equality.  No proved injectivity permits cancelling that map. |
| All reached alpha-output requests fresh and slot occurrences | OPEN | The root-label theorem identifies one positional request, but no accepted source path presently constructs the complete occurrence family. |
| Residual-only source target, cardinality cap, bad-alpha event inclusion | OPEN | The routed probability theorem remains abstract over a supplied target; no selected source target provider exists. |
| Cached outputs/restoration | OPEN / outside this fresh-output slice | A cached output is not a newly sampled router coordinate. |

`FSV8RoutedOutputPrefixConsumer` was reviewed.  Its deterministic statement is
validly conditional on an `Alpha0RootLabeledTrace` for the same master tape
and one exact `(index, output)` occurrence per consumed block.  It correctly
leaves advances unconstrained for the ordinary-value decoder.  Current sources
do not construct those premises or the required source event inclusion, so it
is deliberately not presented as an actual V8 accepted-run theorem.

## Scope

No production source, parser, transcript, q22 profile, 40,282-byte body,
field, verifier acceptance condition, CU claim, or security ledger changed.
There is no new global soundness number, no Fiat--Shamir theorem, no
permitted-access payment extraction, no adaptive ZK result, and no Rust
refinement claim.

## Next primitive

The next useful source work is a **selected V8 configuration refinement** that
constructs—not assumes—the work-script grammar/first-alpha-use fact, the
resource facts, and an exact root-to-local complete-history replay before
`projectRecord`.  It can then use this S2 label theorem to build the four
consumed fresh-output occurrences and, separately, a source-local target/event
inclusion.  Without that selected producer, extending generic `Configuration`
would be false by the retained counterexample.
