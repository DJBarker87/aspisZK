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

The event interface also retains native `.panic`/`.abort` tags. The existing
`actual_factors` source carrier has only `.ok`/`.fail`/`.div`; it does not
magically recover a distinct panic/abort tag from an undifferentiated source
failure. For such paths native acquisition uses `native_factorization` and
the DIAG terminal association in `Links.context`. `Link_Source` is usable only
where its exact source/native terminal equation is actually proved. No panic
or abort tag is silently collapsed in the experimental native experiment.

## Validation and receipts

All four final modules PASS. Successful final receipts are **67801**
(Interface), **67804** (Headline), **67807** (Residual), **67809** (Average).
Their original output includes every added theorem's `#print axioms`; only
`propext`, `Classical.choice`, `Quot.sound` occur in accepted results.
`eventJoin` and `joined` definitions are audited too. `final-manifest.json`
checks each current source against its accepted receipt, every theorem's
audit line, exact bound-token equality, and unchanged protected files.

| ID | Exact target | Exit | Wall | Peak RSS KiB | Swaps | Source revision |
|---|---|---:|---:|---:|---:|---|
| 67800 | PV_EVHD_Interface | 1 | 0:01.75 | 4180836 | 0 | `eac10d07f1fe47088d42353409b298ffaad3e931` |
| 67801 | PV_EVHD_Interface | 0 | 0:01.94 | 4207436 | 0 | `e37ec93e7bc6f8b43aabddfbbf3384dbc0411433` |
| 67802 | PV_EVHD_Headline | 1 | 0:03.45 | 4276324 | 0 | `c9079f93b4f10f2fccbee1ee22f06feb8831cf6a` |
| 67803 | PV_EVHD_Headline | 1 | 0:11.78 | 4303516 | 0 | `c4a39bf04aa3f088b892175377a4fa99e8d935a6` |
| 67804 | PV_EVHD_Headline | 0 | 0:14.01 | 4359852 | 0 | `256af53b05c5e7e90f2199220fa00c238b641446` |
| 67805 | PV_EVHD_Residual | 1 | 0:01.65 | 4170996 | 0 | `ae2954eef6ae589290431f30635a80dcdd5c08a4` |
| 67806 | PV_EVHD_Residual | 1 | 0:01.68 | 4170696 | 0 | `eb50d0310700394716bdfea809835c935ca730df` |
| 67807 | PV_EVHD_Residual | 0 | 0:01.73 | 4193324 | 0 | `54a52b06205179a1737456f5394338cf7617faee` |
| 67808 | PV_EVHD_Average | 1 | 0:16.74 | 4332452 | 0 | `1183106862a62c060debc70f3db1f65c7947cdeb` |
| 67809 | PV_EVHD_Average | 0 | 0:07.41 | 4318776 | 0 | `6f39a32b2b16ae11bd27113ad6d045e9be520779` |

Failures were retained, never retried unchanged: 67800 ambiguous Bytes;
67802 missing R1Z namespace opening; 67803 local log-notation collision and
elided unused parameters; 67805/67806 decidability-instance-sensitive
rewriting of a zero indicator (replaced by pointwise equality); 67808
heartbeat exhaustion in higher-order inference at `apply average_bound`
(replaced by explicit carriers/functions, successful 67809). No memory cap,
heartbeat, recursion or exponentiation threshold was raised. Failed elaboration
logs may print `sorryAx` recovery placeholders; none is accepted evidence and
no such placeholder occurs in the successful audits.

Lean 4.32 githash `8c9756b28d64dab099da31a4c09229a9e6a2ef35`,
-M7000; one scope at a time, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. Every launch chains admission exit 0,
JSON allowed:true check, then scope in the SAME shell command. All admissions
were allowed; no quiet-window/refusal/cooldown bypass occurred.
Original time/output/admission logs and ID scans (all codex-pv job evidence
directories plus shared sent.txt) are retained per attempt.

The source-only failed-attempt guard is in `tools/pv-evhd-20261029/compile.py`.
Its SHA-256 is
`de57f57608caf62e273fef96829589fbfac904332e58e422add3554b3ec50195`.
The final checker executes that actual guard against ALL SIX failed source
hashes and confirms refusal. No unchanged failed source was resubmitted.

Reuse is read-only under (h6): preparations verify the selected EJR/freeze/
tracked/read-only-runjoin source SHA, actual toolchain and LEAN_PATH prefix,
every recorded project import edge, and ALL 5,673 coherent-replay external
object hashes before compilation. Successful own predecessor objects are
SHA-pinned and reused; no inherited module is rebuilt or overwritten.
The Interface object's hash was recovered read-only after its original receipt
and compared before dependent reuse; that timing is marked in receipt-67801.
Preparations are retained per module. Historical dependency vectors point to
the unchanged import closures in those preparations (the source import lists
were mechanically compared at each historical revision); the original
per-launch preparation-file fingerprint is also retained.

- `PV_EVHD_Interface`: 602 project/import object checks; 5673 external hashes.
- `PV_EVHD_Headline`: 811 project/import object checks; 5673 external hashes.
- `PV_EVHD_Residual`: 603 project/import object checks; 5673 external hashes.
- `PV_EVHD_Average`: 812 project/import object checks; 5673 external hashes.

The L1C cache had explicitly deleted its timing objects (its committed
cache-cleanup.json, confirmed by read-only host lookup). Therefore only the
small generic timing reconstruction PROOF TEXT is reused under new PV_EVHD_
names; no nonexistent L1C object is claimed reused. Existing native decoder
and model objects are reused from the pinned RJ4IDB cohort and its verified
Stream B dependency caches. Earlier pv-top had no accepted composed skeleton;
pv-fib's fibre/termination objects are not dependencies of this new carrier,
so no own earlier theorem is needlessly rebuilt.

Budget used: **10/100 Lean attempts**, **0 native scopes**, **0 Kani**.
Only 67800–67809 were launched; audit reserve 67897–67899 is unused because
every focused module includes its full axioms audit. No local Lean, native
measurement, extraction, Rust build, large generated-certificate aggregation
or deployed frozen-manifest replay ran. The final own-source manifest was
checked once after focused targets were green, without repeating Lean builds.
Python syntax and git whitespace checks pass; no evidence file exceeds 20 MB;
no binary/object/archive is committed.

This stopping point is completion of the requested experimental cost draft,
not budget exhaustion, native closure or adoption. Further Lean attempts cannot
instantiate an unspecified clock/failure probability model. The exact open
links and next concrete deliverable are recorded above; the deployed privacy
target is **not yet established**.

Work commits before the final evidence commit (`git log --oneline e90651e952..HEAD`):

```
6f39a32b2b Instantiate averaging carriers explicitly to avoid large type normalization
1183106862 Exercise refusal for every recorded failed source hash
54a52b0620 Prove zero residual pointwise without changing decidability instances
e729634b6f Use the finite mean monotonicity lemma from abort bounds
eb50d03107 Make residual beta reduction explicit and name native query association
ae2954eef6 Add final bound, axiom and failed-source guard checks
256af53b05 Pin successful own objects before dependent reuse
d922fe876e Use explicit event parameters and avoid the model log notation
c4a39bf04a Resolve R1Z names and document experimental integration costs
c9079f93b4 Expose public failure, causal prefix and residual composition obligations
9939335202 Retain the exact headline bound under shared public noise
e37ec93e7b Name the additional joint trace charge when exact links fail
bc5ae5c9f2 Qualify event bytes and retain the source decoder association
eac10d07f1 Compose experimental trace simulator with the unchanged model proof
834968f355 Use the coupling namespace of the charged-event model
ad49740352 Draft experimental event observation and exact joint trace links
```

No push, merge, shared-source edit or root-worktree edit was performed.
