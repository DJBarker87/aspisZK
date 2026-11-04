> D508 follow-up: the authoritative specialised list is now
> [`../pv-evh2-20261029/LINKS.md`](../pv-evh2-20261029/LINKS.md), at the
> partial `PV_EVH_RuntimeBinding.rtDeployed`. Its missing native DATA selections
> and lack of an actual joint witness are explicit; no live-runtime credit.

# Adopted event-retaining privacy links — D502 / D478

This map supersedes `evidence/pv-top-20261029/LINKS.md` for the privacy target.
The target is `R1Z.PrivacyR1HeadlineDeployedEvents.privacy_headline_deployed_events`
(exported by `PV_EVH_Deployed`). The historical Result-only theorem is retained
unchanged. OPEN means that no deployed proof is supplied here. Model algebra
and a model satisfiability instance do not discharge a native link.

All links are ordinary Props, not additions to T. `Links` is their conjunction,
not a whole-refinement hypothesis or a privacy conclusion. The nine acquisition
Props below are the original `PV_RJ4IDB.OpenInputs` definitions, with unchanged
signatures and arbitrary path/prefix indices. The publication link appears once:
runjoin's in-progress `RUNJOIN_PUBLISH_COMPACT` is that same original input.

| Link | Owning line | Status / retained native obligation |
|---|---|---|
| `OpenInputs.RUNJOIN_PUBLISH_COMPACT` | runjoin | OPEN / in progress: actual compact publication, source ordering and caller installation; no invented `publish_compact` equation. |
| `OpenInputs.RUNJOIN_STATEMENT_BYTES` | runjoin/client | OPEN: actual statement and afterstate bytes, including native caller construction. |
| `OpenInputs.DIAG_FILE_TRACE` | diag | OPEN native acquisition: requests, deliveries, errors, recovery, cleanup and durable prefixes. |
| `OpenInputs.DIAG_JSON_STDOUT_TRACE` | diag | OPEN native acquisition: full returned JSON and requested/delivered stdout, including time copies. |
| `OpenInputs.DIAG_ERROR_STDERR_TRACE` | diag | OPEN native acquisition: variants, text, capture PCs, drop/unwind, panic/OOM/abort/crash and earlier prefixes. |
| `OpenInputs.L1_COUNT_TRACE` | L1 | OPEN: original entered/rejected counts, selected accounts, upload/operation counts on the original experiment. |
| `OpenInputs.L1_TIME_TRACE` | L1 | OPEN: serialized clock and physical timing jointly with every other channel. |
| `OpenInputs.L1_ORACLE_PREFIX` | L1/runjoin | OPEN: every ordered query/answer, duplicate, rejected, failure and divergence prefix. |
| `OpenInputs.L1_RETAINED_SIDECHANNELS` | L1/diag | OPEN: allocation, addresses, physical/durable/environment effects and all D159 observations. |
| `PrivacyR1HeadlineDeployedEvents.D163` | L1/runjoin | OPEN: same native acquisition and original model/seed/fuel common carrier, with BOTH exact marginals. |
| `PrivacyR1HeadlineDeployedEvents.OrderedEventContext` | runjoin/L1/diag | OPEN: full ordered non-wall context, terminal tags and embedded clock bytes on the SAME good sample. |
| `PrivacyR1HeadlineDeployedEvents.D166` | L1 | OPEN: exact joint timing on that D163 sample; no independent clock marginals. |
| `PrivacyR1HeadlineDeployedEvents.SignalAgreement` | OS-failure/runjoin | OPEN: option-B signal on that same sample; preceding trace retained. |
| `PrivacyR1HeadlineDeployedEvents.V400` | OS-failure | OPEN: witness-independent public signal distribution for every equal-public witness. |
| `PrivacyR1HeadlineDeployedEvents.PublicEnvironment` | entropy/L1/runjoin | OPEN: actual joint environment/coin acquisition has the named public product law. Native nonuniform/continuous/unbounded noise is not assumed finite uniform. |
| `PrivacyR1HeadlineDeployedEvents.CausalPrefix` | runjoin/L1 | OPEN: progressive completion preserves already emitted events. |
| `PrivacyR1HeadlineDeployedEvents.ObserverProgram` | runjoin/ROM | OPEN: actual adaptive program at every invocation/prefix equals the pullback program, without future-data access. |
| `PrivacyR1HeadlineDeployedEvents.op227` | b3p6/runjoin, V244 | OPEN / in progress: exact existing `selected_callback` binder, every actual public/point/challenges and ALL claims, including every Result/error layer. |

The D163 excluded event remains exactly
`∃ i, ProverCommitFuelJoin22.bad oldBad seedQueries i modelCoordinate`.
`oldBad` is `QueryScanRealLazyBound.realBad` at the original W/Pr/h/B/outputs/x/w;
`seedQueries` is the original adversary-only ordered suffix for the pulled-back
event observer. The full native oracle prefix is a separate retained observation.
No retry, OS failure or divergence has been added to the charged event.

The inherited publication sublinks remain with runjoin: R24 sampler, common
sample, backend input, finish context, QueryAppend with its opening-domain
precondition and explicit QueryRange obligation (D485), NodeAppend and
PublishOrder. The former unconstrained QueryAppend is refuted and cannot be
used. R24's existing model discharge is not a native caller installation.
Native source/provider V045/V163/V165/V167, E1/E2/V329, native fill V336,
ledger V337, byte blindness V338 and kernels V339 remain upstream obligations.
Count V347–V351/V394, weights V258–V260 and coefficient V262 retain their
owning-line statuses. No suspended row is restored by this adoption.

`native_factorization` supplies the lossless native decoder; `actual_factors`
supplies the source Run decoder. `PV_EVH_Interface.source_observation`
composes them only under the source/native event equation. Native panic/abort
use the native decoder directly; the source Run's fail tag is not silently
identified with a distinct panic or abort. The old Result-fibre obligation is
removed from the adopted target, rather than assumed or asserted to hold.

V370 (compiler preservation, pending D381/D386), V371 and rdea-1 remain at
their original boundaries. Allocation success/failure is retained by name under
rdea-1. No own-1 binding, own-2''' singleton execution or b3p6-1 token-identity
reclassification is claimed by this proof-only work. T remains exactly
`PV_RunJoin_TrustItems.{entropy_law,entropy_kernel,observation}`.

The runtime selects the native functions and the full event adversary carrier
explicitly as data. A generic data record is not a supplied live native producer.
The mathematical fibre and the separate two-transaction wrapper witness must
not be reported as an unconditional live client/source association. The fixture
consumer retains `FixturePdaRuntime base` and is reserved for the lead's 16 GiB
aggregation; it supplies no proof of the native privacy links listed above.

Exact links retain the old bound. `PV_EVH_Residual.headline_plus_trace` is the
separate approximate variant, with explicitly named `deltaTrace`; it has no
inherited `< 2^-100` conclusion without an additional bound on that residual.
