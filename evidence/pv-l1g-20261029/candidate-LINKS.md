# Whole-privacy links at the PV_TOP carrier stop

This is the authoritative map for this attempted composition, not a release
closure claim. Names below are existing Lean declarations, record fields or
explicitly identified theorem binders. No `PV_TOP_Link_*` aliases have been
introduced: construction stopped before the links could be installed. OPEN
means the deployed instance is unsupplied; PARTIAL means a conditional/model
composition exists; PROVED below refers only to the stated model fact.
Existing proof status is inherited source evidence, not a fresh replay here.

## Exact obstruction

`R1Z.PV_RunJoin_Deployed.Runtime` fixes these consumer signatures:

```lean
disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
  Result (Output N L C) → View K CommitHandle Aux R1Bat
observerOracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
  Result (Output N L C) → List (Bytes × OracleAnswer)
```

`Output N L C` is a returned publication step paired with final State.
`execute` returns only `Result (Output N L C)`. In contrast:

```lean
PV_RJ4IDB.native_factorization (t : NativeTrace A) :
  nativeObservation t = decoder (modelTrace t)
PV_RJ4IDB.actual_factors (render : Aeneas.Std.Error → Bytes)
  (r : R1Z.PV_W_Threading.Run W Event Aeneas.Std.Error A) :
  actualObservation render r = decoder (sourceTrace render r)
```

Neither equation consumes the Runtime Result. The source Run has `outcome`,
`world`, `calls`; the returned projection erases `calls` on success and erases
both world and calls on fail/div. `Observation.ordered` retains those calls.
Consequently `fun out => decoder (sourceTrace render out)` is not well typed
as either Runtime consumer. There is also no supplied fixed adapter from
the complete `Observation A` into the protocol `View` and observer answer
carrier. The query channel in Observation is byte-paired; Runtime answers
are `Fin 32 → UInt8`, requiring the actual codec association.

This is not repaired by the nine acquisition Props: each relates an
independent actual channel family to a native event projection; none relates
two runs with the same returned Result. They therefore do not imply
`R1Z.PV_RJDec_Factor.Fibres reachable (PV_RJ4IDB.actualObservation render)`.
`PV_RJ4IDB.result_fibres_exact` characterizes exactly the three missing laws:
identical complete ordered prefixes for same-value/same-world successes,
same-error failures, and divergences. For example the abstract Run carrier
permits divergent runs with equal final world and respectively zero and one
visible call. They return the same `.div`, but their ordered observations
differ. This is a carrier witness, **not** a deployed reachability witness.
The existing `PV_RunJoin_WorldDecode33.no_decoder` is explicitly conditional
on such a pair and must not be promoted to a native counterexample.

The first required construction therefore cannot be supplied from the
inspected inputs. Under the user's explicit mismatch-stop rule, no replacement
observer, empty prefix, convenient failure decoder, new Runtime field, or
assumed whole refinement was introduced.

## Fixed definitions versus unsupplied data

Fixed by runjoin: `initialState`, `World`, `coordinates`, `execute`, `rust`,
`observer_program`; adversary is exactly `R1Adv`, observer program is `adv.prog`,
and observation decision is `adv.decide`. Model coins for the endpoint are
`((source.RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape)`.
Fixed by rj4idb: event alphabet, channel projections, lossless decoder and
both factorization equations. These do not construct native producers.

Runtime still takes `world`, `account`, `body`, `disclosed`, `observerOracle`
and `ideal` as data; the boundary and its native associations also remain
inputs. Merely quantifying over this Runtime would leave V045 unresolved.
The template, outputs, statement and actual source/world/public binding are
also not selected by these generic definitions.

## Required bad event and seed-query correspondence

With **exactly** the headline's local `W`, `Pr`, `h`, `B`, and `source`,
runjoin's endpoint defines:

```lean
oldBad := QueryScanRealLazyBound.realBad W Pr 8 h B outputs x
queries := PrivacyR1HeadlineDeployedReal.realSeedQueries
  template outputs x rust observer_program
```

The RunJoin arguments are `(oldBad w)` and `(queries adv w)`. Its common
sample projects to model coins as `r.coins.1.1`. The excluded event is
`∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins`.
`realSeedQueries` is the **adversary-only** suffix obtained from
`ProverCommitObserverQueries19.real` with
`ProverCommitReencode16.observer ProverCommitReencode16.encode
(RomObserverBin.observerMap rust observer_program adv)`; it is not the native
full oracle prefix, which includes rejected/failed source calls.
`PV_RunJoin_Deployed.observer_exact` fixes observerMap to `adv`. The pathwise
native prefix input alone supplies neither this source-query association nor
the original joint coupling agreement. No new bad event or query list is used.

## Link map

Abbreviations in this table expand to exact namespaces:
`OI = PV_RJ4IDB.OpenInputs`, `PS = R1Z.PV_RunJoin_PublishSkeleton54`,
`EP = R1Z.PV_RunJoin_Endpoint.PV_RunJoin_Premises`,
`D10 = PV_DIAG10`, `LC = PV_L1E_CountSkeleton`,
`LO = PV_L1E_OriginalCountSkeleton`.

| Exact Lean name (with namespace expansion above) | Owning line | Status and precise remaining scope |
|---|---|---|
| `OI.RUNJOIN_PUBLISH_COMPACT` | runjoin | PARTIAL: `PS.complete` has seven named inputs; native caller installation retained. |
| `OI.RUNJOIN_STATEMENT_BYTES` | runjoin/client | OPEN: actual statement/afterstate producer. |
| `OI.DIAG_FILE_TRACE` | diag | PARTIAL: conditional skeleton; native acquisition and order open. |
| `OI.DIAG_JSON_STDOUT_TRACE` | diag | PARTIAL: conditional skeleton; native acquisition and order open. |
| `OI.DIAG_ERROR_STDERR_TRACE` | diag | PARTIAL: conditional skeleton; native acquisition and order open. |
| `OI.L1_COUNT_TRACE` | L1 | PARTIAL: original-count skeleton; native original join open. |
| `OI.L1_TIME_TRACE` | L1 | OPEN: exact serialized time jointly with other channels. |
| `OI.L1_ORACLE_PREFIX` | L1/runjoin | OPEN: all ordered native query/answer prefixes. |
| `OI.L1_RETAINED_SIDECHANNELS` | L1/diag | OPEN: all retained channels and cross-channel order. |
| `PS.PV_RunJoin_Link_R24Sampler` | runjoin | PROVED by `R1Z.PV_RunJoin_LinkR24Discharged54.complete` at the model boundary; inherited source evidence, no fresh replay here. |
| `PS.PV_RunJoin_Link_CommonSample` | runjoin | OPEN: actual common-sample association. |
| `PS.PV_RunJoin_Link_BackendInput` | runjoin | OPEN: actual backend producer. |
| `PS.PV_RunJoin_Link_FinishContext` | runjoin | OPEN: actual finish/publication fields. |
| `PS.PV_RunJoin_Link_QueryAppend` | runjoin | OPEN: 22 query appends. |
| `PS.PV_RunJoin_Link_NodeAppend` | runjoin | OPEN: six slots and indices. |
| `PS.PV_RunJoin_Link_PublishOrder` | runjoin | OPEN: ordered serialization. |
| `R1Z.PV_RunJoin_OracleBridge38.selected_callback` binder `op227` | b3p6/runjoin | OPEN: full selected callback equality for every actual claims array at actual public/point/challenges; installed-family success does not discharge it. |
| `LC.PV_L1E_Link_CountAcquisition` | L1 | OPEN: source count acquisition. |
| `LC.PV_L1E_Link_BodyWrapper` | L1 | OPEN: full ordered Trace equality, beyond Result erasure. |
| `LO.PV_L1E_Link_OriginalRetry` | L1 | OPEN: original retry including all prefixes. |
| `LO.PV_L1E_Link_NativeD163` | L1/runjoin | OPEN: native original joint source/world association. |
| `D10.PV_DIAG10_Link_Init` | diag | PROVED for `sourceFile`, `sourceJSON`, `sourceError`; generic Prop not universally true. |
| `D10.PV_DIAG10_Link_Step` | diag | PROVED for the three source recurrences; native installation retained. |
| `D10.PV_DIAG10_Link_Readout` instantiated for files | diag | OPEN: actual native file readout. |
| `D10.PV_DIAG10_Link_Readout` instantiated for JSON/stdout | diag | OPEN: actual native JSON/stdout readout. |
| `D10.PV_DIAG10_Link_Readout` instantiated for error/stderr | diag | OPEN: actual native error/stderr readout. |
| `D10.PV_DIAG10_Link_EventOrder` | diag | OPEN: full native event order. |
| `R1Z.PV_RJDec_Factor.Fibres` for complete observation | rj4idb/runjoin/diag/L1 | OPEN: exact missing Result-carrier compatibility. `result_fibres_exact` is an iff, not an instance. |
| `EP.source_V045` | runjoin | OPEN: fixed source body and provider preservation; V045/V163/V165/V167. |
| `EP.E1_V329` | entropy/runjoin | OPEN as concrete boundary input; T not enlarged. |
| `EP.native_fill_V336` | runjoin | OPEN: actual fill operation. |
| `EP.native_ledger_V337` | runjoin | OPEN: actual reservation ledger. |
| `EP.byte_blind_V338` | runjoin | OPEN: scheduling and frame independence. |
| `EP.kernels_V339` | runjoin | OPEN: actual conditional kernels. |
| `EP.disclosed_V038` | runjoin/diag/L1 | OPEN: complete agreement outside exact bad event; cannot replace this with acquisition alone. |
| `EP.observerOracle_V038` | runjoin/L1 | OPEN: same source observer transcript outside exact bad event. |

The last eight rows are the step-(4) consumer needs, retained for diagnosis;
they are **not** proposed PV_TOP hypotheses. Taking the two V038 fields as
new links would conceal the central agreement obligation the task asks to
derive. Runjoin53/54 reports state step (4) was not started.

Suspended/reduced ledger source claims feeding these needs retain their
existing status: V163/V165/V167 feed `source_V045`; V244 (op227),
V258–V260 (weights) and V262 (coefficients) feed the publication/source cone;
V347–V351 and V394 feed count/original joint observation; V370 (compiler
preservation, D381/D386), rdea-1 and V371 remain retained boundaries. No
suspended row is silently restored by this map. There is no single existing
Lean Prop for each of these ledger rows, so no fictional Lean name is given.
The requested `evidence/privacy-recount-20261026/ROWS8.md` is absent at the
candidate HEAD; the tracked design ledger and owner reports are the evidence
used here. A complete suspension recount is not claimed at this early stop.
