# Native observation inputs — LOG D448

These are unproved producer/association obligations, not axioms, trust fields,
or assumptions of a theorem asserting its own conclusion. No theorem in this
round takes `actualObservation = decoder trace` as a hypothesis. T is unchanged.

`PV_RJ4IDB.native_factorization` constructs the composition of the channels
below on a native event record. `PV_RJ4IDB.all_prefixes` covers every index of
an arbitrary family of finite prefixes. `PV_RJ4IDB.actual_factors` proves the
corresponding equation on `PV_W_Threading.Run W Event Error A`. The missing
native producers are NOT supplied by the existence of either data type.

| Named open input (one per component) | Owner / exact producer | Required input |
|---|---|---|
| `RUNJOIN_PUBLISH_COMPACT` | runjoin; `prover.rs` publication; runjoin step (2) and later publication | Compact proof bytes from the actual successful published record. No `publish_compact` equation was found in the pinned read-only runjoin PV_RunJoin modules. `PublicationInput.publish_compact` is the explicitly named byte input until that equation exists. |
| `RUNJOIN_STATEMENT_BYTES` | runjoin/client; `plan.rs:114`, semantic public at :116; terminal codec | Exact encoded statement and candidate-afterstate bytes at the actual caller. CallerLive proves the byte-pinned payment/lane projection, not native construction of that record. |
| `DIAG_FILE_TRACE` | diag; `plan.rs:109–119`, `DurableStateOnlyMaskNonceStore` | Complete ordered native file create/write/sync/request/delivery/error/cleanup trace, including recovery and ledger prefixes and both publication files. Requested bytes are distinct from delivered bytes. |
| `DIAG_JSON_STDOUT_TRACE` | diag; `plan.rs:129`; `devnet_spend.rs:13` | Exact returned JSON, formatting/allocation, requested/delivered stdout bytes and normal/panic/abort/divergent continuations. The JSON contains audit text, addresses, instructions, byte/upload counts and timing; these are not replaced by proof/count alone. |
| `DIAG_ERROR_STDERR_TRACE` | diag; PV_DIAG2/PV_DIAG3 models and their open native leaves | Occurrence, variant, text, capture PCs, formatting, stderr request/delivery, ownership/drop/unwind, panic/OOM/foreign/crash register and memory payloads, including every earlier prefix. `diagWithState` additionally retains the final visible-state projector, including failure/divergence post-state. Unit-error content lemmas discharge only content selection after a variant is known. |
| `L1_COUNT_TRACE` | L1; D163, V394, V347–V351; `result.attempts` and account selection | Same original experiment/coupling for entered/rejected prefixes, successful published count, selected account, upload/operation counts. ReturnedOutput proves the existing model's returned count; no new marginal count coupling is invented. |
| `L1_TIME_TRACE` | L1; `plan.rs:84,129`, `Instant::now/elapsed/as_secs_f64` | Exact serialized `prove_wall_seconds` and all retained timing observations jointly with the other channels and failure event, rather than zero/constant time. |
| `L1_ORACLE_PREFIX` | L1/runjoin; ROM observer and full source-world call log | Every ordered query/answer, duplicate, rejected attempt, failure/divergence prefix. The old Result's failure/divergence constructors contain no call prefix. |
| `L1_RETAINED_SIDECHANNELS` | L1/diag; D159/D162/D166/D348 | All remaining retained allocation/address/physical/durable/environment observations and cross-channel order, with the same failure coupling. Recovery data is retained in the file trace; it is not exported as private key material or declared public. |

## Old Runtime compatibility

`PV_RJ4IDB.result_fibres_exact` is the exact necessary-and-sufficient
condition for the FULL ordered-event observation to factor through the old
returned Result: same-success-value/final-world fibres, every same-error
failure fibre, and the divergence fibre must have identical visible event
prefixes. `component_cases` gives the corresponding three clauses for each
component. This is an audited characterization, not a supplied native law.

The six `output_disclosed_*` / `output_oracle_*` clauses are proved for the
available complete returned-output component (proof, count and EVERY terminal
tag), under unchanged consumer functions. `DecoderCases` also supplies the
six total-extension equations for explicit pullback decoders. These equations
must not be reported as a concrete installation of Runtime.disclosed or
Runtime.observerOracle: those require the open native component producers
above AND their prefix-fibre laws. No empty oracle, fixed failure observation,
unreachable-result convenience extension, or post-failure empty history is
chosen. Entropy/body/initial-state hypotheses of CommonCases remain unchanged.

## Other dependencies

* op79: V201's 145 concrete ChunksExact/Zip/array-iterator/index records belong
  to pv-rdcd3. This round does not redo that work or credit its pending result.
* op254: source/Result association is addressed by NativePowers plus the
  source binding and deployed-configuration finite validation. Source-to-code
  remains V370 at pending owner D381/D386; physical/crash observations remain
  in the components above.
* V047: the intended native request/world/compiled-afterstate and actual
  commitment handle still need their native source binding to CallerLive's
  pinned record. The general live plan is not universally transfer-13.
  FixturePdaRuntime is not used by these mathematical projections; it remains
  explicit and unproved for any joint-wrapper claim.
