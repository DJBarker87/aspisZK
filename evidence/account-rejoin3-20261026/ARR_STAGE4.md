# ARR stage 4: bounded dependency restoration and unchanged-top ledger

99/100 actual Lean invocations through label100; one prelaunch label002 did
not invoke Lean. All79 missing unchanged dependency builds passed. Own focused
results are the27 theorems named in ARR_FinalAudit (one final audit remains).
No original dependency module was source-edited; receipt snapshots retain exact
canonical source hashes. No package or manifest replay was run.

ARR_BEFORE/AFTER_SOURCE are literal identical Rc10 source; inherited complete
kernel prints are separately labelled by ARR_KERNEL_PROVENANCE.json.
ARR_validate.py independently recomputes all atomic row counts from the frozen
Rc10 ledger: actual83T/12P/13G, distinct non-alias combined89T/16P/13G;
L185 aliases L159. No row removed/added/reclassified. No ARR deployed top exists.

The budget has one compiler invocation left, reserved for the single final
standard-axiom/signature audit on delivered ARR modules. Missing old account/
root dependencies remain; no fresh actual-root kernel audit is claimed.
