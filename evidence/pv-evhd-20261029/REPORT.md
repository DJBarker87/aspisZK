# EXPERIMENTAL, NOT ADOPTED — D478 event-retaining headline draft

Branch `codex/pv-evhd-20261029`; base candidate `e90651e952`.
Worktree exactly `/Users/dominic/ZK/.worktrees/pv-top` (sparse).
This is an owner-review draft, not adoption and not established deployed privacy.
All definitions/proofs added by this line live in new `PV_EVHD_` modules.
The deployed headline, Runtime, simulator, observer, bound, implementation and
release pins are unchanged. No keys were created, changed or removed.

## Interface and experiments

`PV_EVHD_Interface.observe` returns the option-B signal paired with the exact
`PV_RJ4IDB.Observation A` produced by `nativeObservation`: ordered events,
terminal outcome, files including partial operations, stdout/JSON, diagnostics,
counts, serialized timing, oracle history and retained side channels.
`source_observation` composes `actual_factors` and `native_factorization` under
the explicit `Link_Source` source/native event equation. No Result decoder,
fibre law or assumption of successful return is used.

`PV_EVHD_Headline.real` observes the native trace and native signal directly.
`Completion` supplies a public, witness-free joint completion kernel from the
public invocation, option-B signal, environmental noise and the model ROM view.
The completion also sees the retained model oracle log. `ideal` first runs the
UNCHANGED mathematical simE through the existing source experiment, then uses
that completion to generate the full trace. Environmental failure does not
replace the whole observation with a constant error: the preceding prefix is
retained and must be simulated. No Rust simulator premise is introduced.

The observer's `program` and `decide` both receive the signal and full trace.
`observer` pulls them back to the existing `R1Adv` program/decision interface.
`PV_EVHD_Average.realExperiment` and `idealExperiment` sample the same public
finite environmental/noise carrier jointly with their respective game coins.
The latter has no witness argument. `draft_headline_joint` averages the
conditional theorem without conditioning on success or signal.

The native producer, completion, public input and observers are parameters,
not a claim that a deployed instance is supplied. Every fixed public invocation
and every observer/witness is quantified. Public data must not include a
witness, secret coins, actual elapsed time or desired trace. The public failure
signal is ONLY the owner's option-B signal, not the whole prefix.

Every finite divergent prefix can be supplied to the interface; no terminal
Result erases it. For privacy against an arbitrary public stopping/prefix
policy, the native links must hold for each such policy as public invocation
data, including all prefix families. A finite trace record does not by itself
prove a probability theorem about an entire infinite stream. The draft uses
the existing finite-uniform mean/coupling framework. Native continuous,
nonuniform or unbounded scheduling/noise has NOT been silently identified with
that carrier; its joint marginal/measure extension is named in COST.md.

## Exact bound and named proof links

`PV_EVHD_Headline.bound template outputs x` is definitionally the existing
headline expression, with W/Pr/L₁/L₂ exactly as in the endpoint:

```
modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486
  + QueryScanFreshUnion.freshBudget (8 * n1 W Pr + 1)
  + 2 * ProverCommitSeedEvent19.budget (2^64)
  + 2 * ProverCommitFuelMass22.charge
```

`draft_headline` retains its numerical envelope and <2^-100 conjunct. These
conjuncts apply to the SAME bound, conditional on the exact event links; they
are not a claim that the native instance satisfies them. The charged complement
is exactly `¬ ∃ i, ProverCommitFuelJoin22.bad old queries i (cp.toM s)`, with
`old := QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w`. `seedQueries`
is the original adversary-only suffix for the pulled-back event observer,
including the original ordered reencoding. It is not the entire native log.
No OS failure, retry rejection or divergence is newly declared charged.

| Exact name | Existing proof transfer / new work | Status |
|---|---|---|
| `PV_RJ4IDB.native_factorization`, `actual_factors` → `PV_EVHD_Interface.source_observation` | Decoder equations transfer unchanged; `Link_Source` requires actual source/native event association. | Algebra PROVED; native link OPEN |
| `PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted` | Used unchanged for the fixed numerical model envelope. Its inherited premises/tool boundaries are not removed. | REUSED unchanged |
| `ProverCommitModelCore16.core_privacy` | Applied unchanged to the same model and public premise/caller laws. | REUSED unchanged |
| `ProverCommitReencode16.privacy_transport` | Applied unchanged to the event observer pulled back by `PV_EVHD_Headline.observer`. | REUSED unchanged |
| `PV_EVHD_Headline.observer` | New program and decision adapter, parameterized by the public completion; no witness input. | DEFINED; native scheduling association OPEN |
| `PV_EVHD_Residual.Link_CausalPrefix`, `Link_ObserverProgram` | Necessary progressive event stability. The actual source query-program equality and absence of future-data use must also be established. | OPEN |
| `PV_EVHD_Headline.Links.cp` | D163 common carrier with both exact marginals and model/seed/fuel coordinates. Old Result-level agreement does not produce this extension. | OPEN |
| `PV_EVHD_Headline.Links.context` / `PV_EVHD_Interface.Link_Context` | Full non-wall context/order and terminal, including failed/divergent and rejected prefixes. Requires joint mask/count/oracle/DIAG/side-channel simulation, not separate projection marginals. | OPEN |
| `PV_EVHD_Headline.Links.timing` / `PV_EVHD_Interface.Link_Timing` | D166 timing equality on that same good common sample. Reconstruction lemma is reused from L1C proof text; no native clock law is assumed proved. | OPEN |
| `PV_EVHD_Headline.Links.signal` / `PV_EVHD_Interface.Link_Signal` | Actual option-B signal agrees on that same sample. Full prior prefix is still part of context. | OPEN |
| `PV_EVHD_Residual.Link_PublicSignal` | Witness-independent public failure distribution for all equal-public witnesses, separately from its prior prefix. | OPEN |
| `PV_EVHD_Residual.Link_PublicEnvironment` | Exact JOINT environment/entropy marginal, not just equal signal or time marginals. Associates actual execution to the finite public product experiment. | OPEN |
| `PV_EVHD_Interface.full_agreement`, `eventJoin`, `PV_EVHD_Headline.joined` | Reconstructs complete trace and the original RunJoin from context, timing and signal links. Existing `ProverCommitFuelJoin22.test_bound` then transfers unchanged. | Conditional model algebra |
| `PV_EVHD_Average.average_bound`, `draft_headline_joint` | Joint public-noise averaging preserves the bound without conditioning away failures. | Conditional model algebra |

The nine pre-existing `PV_RJ4IDB.OpenInputs` remain native acquisition links:
`RUNJOIN_PUBLISH_COMPACT`, `RUNJOIN_STATEMENT_BYTES`, `DIAG_FILE_TRACE`,
`DIAG_JSON_STDOUT_TRACE`, `DIAG_ERROR_STDERR_TRACE`, `L1_COUNT_TRACE`,
`L1_TIME_TRACE`, `L1_ORACLE_PREFIX`, `L1_RETAINED_SIDECHANNELS`. Their owners
and unfinished native P obligations are retained, as are op227, publication,
count/query and DIAG source laws in the pv-top LINKS map. These links do not
on their own establish cross-channel order or the joint simulator.

The crucial timing detail: `timingKey` erases `.wall` payloads only. A time
value also embedded in `.returned` or `.printed` bytes remains in its context.
Consequently the context link must synchronize those bytes using the SAME
noise as the wall field, or fail. No proof here wrongly treats equality of
wall samples plus equality of time-erased stdout as automatic. Physical or
external timing observations must be encoded in retained side channels and
covered jointly too, without a zero-time convention.

If exact simulation cannot be proved, `PV_EVHD_Residual.traceResidual` names
`eventMass (fun s => ¬bad s ∧ real s ≠ sim s)`. `with_residual` charges this
additional JOINT disagreement once, outside the old event; `exact_links_zero`
proves it vanishes under the exact links. `headline_plus_trace` displays the
old bound plus `deltaTrace` for an explicitly bounded real/surrogate gap.
A timing-only term is valid only after all other context/signal equalities,
including embedded clock bytes, have been supplied. No positive term is
proved necessary or bounded for native execution. D166 asks for exact joint
simulation up to existing events, so no additional term is forced merely by
changing the observation carrier. Silently assuming exact timing, or silently
retaining the old numeric <2^-100 claim after adding error, would be invalid.

## Premise delta, limitations and next deliverable

Before: the deployed headline has the sole `RustRealRefinement` premise through
Result-only observations. After: that SAME headline and premise remain
unchanged. Removed from the deployed endpoint: **none**. Added to it or to T:
**none**. The experimental theorem takes a different event carrier and named
ordinary proof links; grouping them in `Links` is organization, not discharge.
Its new links are not asserted as cryptographic assumptions or extra trust.
Existing `entropy_law`, `entropy_kernel`, `observation` remain the only T fields;
V370 compiler preservation and all current native P boundaries remain retained.

The draft shows the observation-layer algebra can carry the old bound; it does
not solve the joint trace simulator. In particular no current theorem proves
that rejected private-coin traces can be completed from model public view and
public noise with the required joint law. F3/F5/F6 and L1 source cost laws must
supply that result, extending the model/source composition where needed.

The inherited model's adversary is `R1Adv`, a post-proof adaptive ROM observer.
Installing the event adapter requires its program to match actual scheduling
without future information. No theorem here extends the core game to arbitrary
concurrent prepublication oracle interaction. If the target requires that
stronger schedule, that is a separate core-model extension, explicitly costed
as unresolved rather than assumed away.

Next concrete deliverable after owner choice: specify the native public
clock/scheduler/failure probability model and a progressive completion kernel,
then prove `Links.context` for one full successful **and failed** prefix family
on the D163 common sample, synchronizing wrapper timing/JSON/stdout. That will
determine whether the exact D166 route suffices or a separately justified
joint trace error is needed. See COST.md for the obligation-level estimate.
