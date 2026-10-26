# SCB stage 2: exact L159 obstruction and mandatory stop

SCB_PhysicalRun.runtime ghost-records exactly one original execution, with
canon P, returning its complete chronological RunView. runtime_eval checks
both the outer physical log and the returned view. not_binding proves that
L159 fails whenever that verifier execution accepts and has a nonempty log.
countermodel supplies both conditions with an explicit one-query verifier;
no false acceptance hypothesis is used for that model.

SCB_SourceReplay.installed_physical derives Physical for the literal
DrvC_SourceEntry.source at every Configuration. installed_single_run applies
the exact L159 obstruction to that installed source on lift P, with its
accepted/nonempty observations explicit. It does not assert a fully
instantiated cryptographic source fixture. Frozen3 changes no part of this
source-side annotation equation: no frozen2 decision or model join occurs.

The precise necessary chronological sub-obligation is ReplayLogLaw:

    forall H run, eval(H,runtime).output = some run -> run.accept = true ->
      let v = eval(H,originalWith rust (canon P))
      run.log = v.log ++ eval(H,rust(v.input)).log

log_of_binding derives it from L159. If run is the physical v required by the
task, this equation forces the verifier log to be empty. None of
RuntimeEntrypointAdmission, RuntimeSyscall, Allocator, CheckpointVersionBinding,
RuntimePersistence or approved game clauses (a)-(d) requires a second verifier
execution or inserts a virtual replay into the physical chronological view.
In particular field(d) is physical CP-action correspondence, not a log-replay
instruction. Adding this law to a nonempty accepted physical execution would
be inconsistent; it must not become another runtime trust item.

The explicit owner stop condition now applies. Proof development stops before
spending the remaining budget on wrappers or hiding this log clause in a
certificate. Only the focused final statement/axiom audit and receipts remain.
Recommendation to lead: retain the physical source run and prove a separate
annotation observation/transport theorem, accounting for its ghost enrichment
and repeated known-cell suffix. That requires an endpoint/interface change;
it is not premise removal from the unchanged Rc4 top. No such change is made.

Validation: SCB_004 exit0, 1.711464244s, 4,290,984KiB RSS, swap0;
SCB_005 exit0, 2.467448899s, 5,295,680KiB RSS, swap0; revision54e9da6401
plus exact per-target dirty source hashes. All nine new theorem audits use
only propext, Classical.choice, Quot.sound. Same capped host commands/cache
and resource reservation barrier as stage1; no contention refusal or retries.

Before/after actual-top statements: unchanged Rc4_Top.deployed. L159 remains
one P quantified family; L185 remains its deployment alias, not another
independent family. Actual and deployment-inclusive T/P/C deltas are all0.
No SCB_Top.deployed, no security conclusion, no discharged ledger row.
