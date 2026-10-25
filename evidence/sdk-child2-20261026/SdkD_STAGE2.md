# Stage 2: same-witness Uni and Tx2N composition

SdkD_Accepted.accepted_pair_unified checks (attempt023) on ONE f,s,cuts.
It retains every Uni conclusion, uses the concrete child and accepted-only
marks internally, specializes TX2's source dictionary to Tx2N_Execution.control,
and derives Tx2N_Finish.Outcome on THAT s.pub/s.proof/s.checkpoint and saved Vec.
SdkD_Inner.same_pair consumes the same cuts and RowOrder_History result;
there is no independently selected accepted pair or compatibility hypothesis.

No claim that authenticated_S1 is removed: it remains inside Outcome's
continuation, exactly as does the physical TX1 writer equation and other
primitive/finish laws. The free stage dictionary is specialized to the
named installed inner bodies, as in Tx2N. No new trust item or source equality
hypothesis is added. Only the control-site child and marks have been supplied.
No global source budget, preparation/root provenance or security endpoint
instance has been established. The100-bit target remains not established.

23 Lean attempts used,0 Kani. 020's incorrect namespace qualification and
unresolved operation metavariables were corrected;021 passes the isolated
same_pair helper. 022 omitted the stage specialization in three fields of
the copied statement;023 corrects those and passes. No timed-out or killed
job was repeated. No new caps/options, existing-module edit or launcher change.
023:exit0,2.887607312s,5224408KiB RSS,swap0,standard three axioms. Exact commands,
revision anchors, hashes, dependencies, caps and full audits are in receipts.
No shipped/cfg(kani)/artifact change, no full replay or key activity.
