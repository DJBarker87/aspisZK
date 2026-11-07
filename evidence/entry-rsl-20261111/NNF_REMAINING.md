# NNF remaining obligations

Target not yet established. All four complete parameterized canonical RSL folds compile, are library-parametric and match TAS via NNF_TAS.roots. No self-credit.

| Member | Exact remaining obligation |
|---|---|
|TX1:333 process|Instantiate NNF_Folds.process_tx1 with actual canonical NMV344 and NMV240 packets. Both admitted routes are part of this single frozen body, so both packets are required. The actual wrapper producers remain the separate sibling obligation.|
|TX2:221 process|Same full packet and SAME unchanged arguments as333; instantiate NNF_Folds.process_tx2. No equality of stage2 native and canonical model off Root0 is needed.|
|TX1:330 entry|Instantiate NNF_Folds.entry_tx1 with the complete process333 root; rejection and all process own-input caller clauses are already proved.|
|TX2:213 entry|Instantiate NNF_Folds.entry_tx2 with the complete process221 root; weak library entry is unconditional after wrapper packet installation. Canonical Root0 occurrence comes from G1c/top, never a new global premise.|
|TAS binding|Use NNF_TAS.install for the shared Impl process/entry fields. NNF_Reify proves this interpretation is the fresh emitted body on all Rust-representable original arguments. If a physical adapter chose a distinct interpreter, it must prove that representation equality; no equality of arbitrary Impl functions is assumed here.|
|Validation|DONE:23 own raw ax2 roots, exact TAS fields, L021 focused ledger24 import, L023–25 pin batches, L028 export, local evidence validation PASS.|

There is no dispatcher obligation requiring Kani or extraction: both budgets are zero, NMW emission is the authorized route. The remaining native wrapper/child producers are owned by NMV/NMT/NMS; duplicating their work is out of scope. No claim of release or 100-bit target closure.
