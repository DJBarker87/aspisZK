# PV_DIAG6 — D454 diagnostic continuation

Target not yet established. Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`, branch `codex/pv-diag6-20261029`, base `19b2164e3d`. V2 is done and is not replayed.

## Native joint-event and terminal control

`PV_DIAG6_Native` supplies named joint laws for unwind, lexical scope, write-all step and arbitrary finite write prefixes, dynamic/static formatting, adapter error storage, stderr capture dispatch, ignored write Results and owned Termination reporting. The relational contracts retain ordered events, final state and terminal together. All primitive native callee coupling laws remain explicit hypotheses. In particular these are **control composition laws, not concrete native privacy instances**.

The abnormal leaf, Interrupted guard and Interrupted-error destruction laws retain precisely the already-emitted prefix on panic, abort or divergence. The adapter retains error-slot replacement effects; formatting and capture failures do not fabricate later calls. Existing source regions are rechecked in `source-bindings.json` against deployed rust-src1.94.1/dependency file hashes, retaining allocator, syscall/errno, vtable/drop, formatter/lock/TLS and memory-validity obligations. V370 / pending D381/D386 remains P. The inherited feature inventory is recorded; no shipped code or feature selection changed.

65200–65207 freshly rebuild the eight smallest inherited model modules. 65208 failed because the unwind proof had not unfolded the model; corrected65209 passes. 65211 failed on a reduced Nat match before the conditional split; corrected65212 passes. No failed object is consumed. 65210 and65213–65242 pass, adding one control/terminal law per incremental source change. native01 rechecks ten complete source regions; it is a source-association check, not runtime or singleton-domain evidence.

Further stages and final audit follow below.
