# NNG remaining — revision4 continuation

Target not yet established. Start of continuation:556 actual Lean/link/audit scopes used;274 remain under the lead's current allowance. No Kani or extraction is planned. Child-first order is094→328→345.

- TX1:136/137/087: previously complete audited candidates retained.137/087 merged in ledger27 per lead. Recompile only dependencies affected by revision4; no unchanged audit rerun.
- TX1:094: COMPLETE audited candidate79c6fd713d3, root NNG_Candidate094.candidate at LIB_Instances.VL/P and corrected ProducerFull094. Full SAME-call domains discharged, including R4 via r4_of_scan and P1880 at checkpoint. L960 combined and L963–L974 raw audit pass; all134 new roots standard-only. Ledger gate decides credit.
- TX1:328: instantiate completed094 and forward its new P1880 clause from328's Domain at unchanged public_bytes; then commit candidate.
- TX1:345: instantiate completed328; P1880Discharge for concrete LIBC_S1 is checked in NNG_P1880Discharge.decoder (L801), standard axioms, raw audit PASS L963–L974. Discharge caller clause with p1880_of_decode at the SAME successful decode arm.345's Domain staysTrue.
- TX1:344/333/330: follow345 through the existing NMV_/NNF_ folds, with no new caller clause.

NNG_REV4_REBUILD_PLAN.json records108 affected private dependencies with exact source hashes, refreshed by existing capped admission/launcher one module at a time. NNG_R4_objects takes precedence over retained F9 and historical objects. NNG_REV4_ORCHESTRATION.jsonl records pausing only the local sequential refresh driver while its current child finishes, to check new small lemmas; never two job scopes. No shared infrastructure/cache or source/spec/trust/shipped file change.

Revision4 current work:094 source fold is partial. Passing QueryTail094 and WeightsTail094 are internal support, not RowSpec094. Remaining fold occurrences: geometry, batch0, checked folded-root copy, initializer, prepare and parsed marker/zero, scan, parse, guard, then exact Ref conversion. Original public Domain+P1880 is retained. New own roots still require raw audit.328 and345 follow child-first only after094 candidate;345 can use proved NNG_P1880Discharge.decoder. No independent new row is claimed closed.

L919 supersedes the partial094 fold status: full concrete094 candidate now compiles. Remaining: own-new-root raw ax2 + focused combined import; instantiate094 at328's original call and error/log callback; then345 at SAME decoded/validated statement and snapshot with P1880Discharge. No094 input clause was added beyond canonical rev4. Ledger gate alone decides credit.

L931:328 complete concrete candidate now exists; commit immediately. New328 root audit pending.345 remains, followed by344/333/330 instantiations.094 raw audit already complete and is not rerun unchanged.
