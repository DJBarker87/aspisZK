# PV_DIAG6 — D454 diagnostic continuation

Target not yet established. Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`, branch `codex/pv-diag6-20261029`, base `19b2164e3d`. V2 is done and is not replayed.

## Native joint-event and terminal control

`PV_DIAG6_Native` supplies named joint laws for unwind, lexical scope, write-all step and arbitrary finite write prefixes, dynamic/static formatting, adapter error storage, stderr capture dispatch, ignored write Results and owned Termination reporting. The relational contracts retain ordered events, final state and terminal together. All primitive native callee coupling laws remain explicit hypotheses. In particular these are **control composition laws, not concrete native privacy instances**.

The abnormal leaf, Interrupted guard and Interrupted-error destruction laws retain precisely the already-emitted prefix on panic, abort or divergence. The adapter retains error-slot replacement effects; formatting and capture failures do not fabricate later calls. Existing source regions are rechecked in `source-bindings.json` against deployed rust-src1.94.1/dependency file hashes, retaining allocator, syscall/errno, vtable/drop, formatter/lock/TLS and memory-validity obligations. V370 / pending D381/D386 remains P. The inherited feature inventory is recorded; no shipped code or feature selection changed.

65200–65207 freshly rebuild the eight smallest inherited model modules. 65208 failed because the unwind proof had not unfolded the model; corrected65209 passes. 65211 failed on a reduced Nat match before the conditional split; corrected65212 passes. No failed object is consumed. 65210 and65213–65242 pass, adding one control/terminal law per incremental source change. native01 rechecks ten complete source regions; it is a source-association check, not runtime or singleton-domain evidence.

Further stages and final audit follow below.

## Failure and divergence prefix recovery

`PV_DIAG6_Prefix` defines a proof relation for ordered list prefixes and a coherent family of finite execution observations. It proves lossless recovery for each family member, permanence and order of all prior emissions, cleanup panic/abort/divergence, partial writes and Interrupted-error destruction. The model result `no_finite_summary_for_unbounded_emissions` forbids replacing an unbounded emitting history with one fixed finite prefix. It is not a native counterexample.

`recover` is a parameter for the existing decoder's errorsStderr3 projection, whose universal equation is `PV_RJ4IDB.diag_events`. No decoder is duplicated. The candidate tree at19b2164e3d still lacks all actual PV_RJ4IDB modules; the inherited read-only branch snapshots identify the consumer. Integration and concrete runtime.disclosed/observerOracle recovery remain P, rather than being inferred from these parameterized laws. 65243,65245–65268 pass;65244 failed on the orientation of list append associativity and was corrected before use.

A first stage commit was delayed by an own-input sparse path omission; `git sparse-checkout add evidence/pv-diag6-20261029` resolved it. No full checkout or compiler launch was involved.
