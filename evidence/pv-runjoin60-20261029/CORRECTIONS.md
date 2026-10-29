# Actual-family and provenance correction (ruling v)

The release target and frozen source are unchanged. Historical links remain
available unchanged for counterexample auditing. The new interface is
`PV_RunJoin_PublishProduced60.Links`; its witness is still required.
`PublishActual60` is an intermediate all-Phase specialization, not the final
source-produced interface and not a witness.

Let `P = {p : Phase // ActualProvenance60.Produced p}` and
`r p = NativeCallback55.runOf ActualRun.data ActualRun.plans p.val`.
`Produced` is the exact successful `NativeControl55.run capture` prefix,
where `capture p = ok (.Ok p)`. It contains no publication, append, model
assembly, backend-message, or sample correctness premise.
`CaptureSource60.produced` derives this predicate from a successful callback
execution with the same input, audit and nonce-store output. Thus restricting
to P does not discard any actual successful native execution.

All predicates below retain their original conjuncts and equalities. Every
remaining model association remains an obligation, rather than an added trust
item. A conditional theorem does not discharge those obligations.

| Link | Before | After |
|---|---|---|
| R24Sampler | Global neutral canonical multiplication and sampler laws | Identical global law; no Fields or Run parameter exists to restrict |
| CommonSample | `R24 -> forall i prepared, prepare(r i)=Ok prepared -> Sample(data i) /\ stored projections` for arbitrary Run families | Same complete conclusion and implication over `i:P`, fixed actual families |
| BackendInput | `forall i prepared, prepare(r i)=Ok prepared -> canonical coefficients /\ hinput /\ length=29` | Identical requirements over `i:P`, fixed actual families |
| FinishContext | Actual prepare/salts/finish success plus canonical coefficients, caller and image laws imply Fields | Identical implication over `i:P`; no arbitrary model Data/Plan parameters |
| QueryContext | Successful prepare/salts/finish chain gives publication provenance | Identical law over `i:P`; proved by retaining those exact source equations |
| QueryRange | Successful prepare/salts/finish chain gives every query `<262144` | Identical law over `i:P`; specialized merged source theorem |
| QueryAppend | `forall i pub, Fields(r i) pub -> ...` (54); range plus publication context added in 57 | Every original conjunct over `i:P` with both strict QueryRange and the exact QueryContext chain |
| NodeAppend | `forall i pub, Fields(r i) pub -> six slots /\ indices law /\ append law` | Every original conjunct over `i:P` with both strict QueryRange and exact QueryContext, using merged RJN correction |
| PublishOrder | Conditional serializer assembly for arbitrary Fields publications and arbitrary families | Same query/node conditional and exact ordered-byte conclusion, over `i:P` with range and publication provenance |

QueryContext removes substituted query arrays, folded words, trees and
commitments which no successful finish of that exact phase returned. The
source-phase restriction also removes arbitrary backend/semantic combinations
never passed by the native builder. The independent source capture theorem
carries the formerly missing obligation that the actual caller reaches that
restricted domain. No append or Fields requirement for an actually produced
publication is removed. QueryRange remains explicit, not silently assumed.

For the intermediate slice model, the source-outcome guard is the historical guard:
all errors, panics and divergence observe None; successful proof bytes are
not read to construct model bytes. The model reads the captured prefix and
assembles its fixed actual Data/Plan families. Auxiliary afterstate/path
fields remain the proof-slice placeholders from round 59; no complete account
or observer association is claimed.

Ruling (v) still requires an explicit non-degenerate simultaneous-link model
witness. Capturing a reachable domain and proving a conditional composition
is not that witness and earns no decomposition or endpoint removal credit.

## Exact original native consumer

`PV_RunJoin_NativeOriginalPublication60.complete` (accepted 69964) has the
existing native `NativePublication55.actual store` and existing
`NativePublication55.published ActualRun.data ActualRun.plans store` as its
two arguments to `RUNJOIN_PUBLISH_COMPACT`. Neither observation function is
replaced or weakened. It consumes only `PublishProduced60.Links`.

`CaptureFactorSource60.complete` factors the full native Result through the
captured prefix, including every Err/fail/div case, original audit and returned
nonce store. `ProducedVariant60.actual` proves S2 from that prefix without
assuming a native builder validity flag. `ProducedCallback60.complete` applies
the slice theorem only at the captured actual Phase. `CapturedTransport60`
then reinstates the original full native model. This is the formal transport
argument for the quantifier correction; the intermediate globally guarded
`NativeProducedPublication60.published` is not used by this final theorem.

This remains a conditional theorem. No witness of `PublishProduced60.Links`,
non-degenerate successful model run, original toRP record association, or
complete Endpoint P discharge follows from it alone.

## Exact declaration substitution

For each row below the “before” is the indicated existing predicate applied
at arbitrary `runs : I → Run`; the “after” is the same predicate applied at
`PV_RunJoin_ActualProvenance60.runs : ActualPhase → Run`. The complete bodies
are retained by abbreviation in PublishProduced60. This is a simultaneous
substitution, including the query/node link arguments inside PublishOrder,
not a deletion of conjuncts within a body.

| Body retained verbatim | New declaration in PublishProduced60 |
|---|---|
| PublishSkeleton54.PV_RunJoin_Link_R24Sampler (no runs argument) | PV_RunJoin_Link_R24Sampler |
| PublishSkeleton54.PV_RunJoin_Link_CommonSample | PV_RunJoin_Link_CommonSample |
| PublishSkeleton54.PV_RunJoin_Link_BackendInput | PV_RunJoin_Link_BackendInput |
| PublishSkeleton54.PV_RunJoin_Link_FinishContext | PV_RunJoin_Link_FinishContext |
| PublishContext57.PV_RunJoin_Link_QueryContext | PV_RunJoin_Link_QueryContext |
| PublishSkeleton57.PV_RunJoin_Link_QueryRange | PV_RunJoin_Link_QueryRange |
| PublishContext57.PV_RunJoin_Link_QueryAppend | PV_RunJoin_Link_QueryAppend |
| PV_RJN_NodeContext.PV_RJN_Link_NodeAppend | PV_RunJoin_Link_NodeAppend |
| PV_RJN_NodeContext.PV_RJN_Link_PublishOrder | PV_RunJoin_Link_PublishOrder |

The 54-to-57 and merged RJN provenance preconditions, where present, remain
explicit in these bodies. Their obligation is discharged for each actual
successful publication by QueryContext and QueryRange, rather than being
assumed from Fields. The new ActualPhase restriction is discharged by the
native prefix capture/factorization. Thus every original requirement on an
actual native successful run is still consumed by the exact original target.
R24 remains global because it has no Run or Fields domain to correct.
