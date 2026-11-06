# PCD CPI scope

Draft parent state/event carrier defined before any native attempt on POOL:350/347/348.
PCD.State threads one NLF parent loan ledger, full account views, the return-register projection and CPI history.
PCD.bind retains complete ProgramError, abort/divergence and the exact effect prefix without post-abort cleanup.

Deployed POOL:348 source sequence: require program; split proof transport; checkpoint distinct;
require exactly two registry accounts; metas [proof,master,checkpoint,lane,registry,entry],
all signer=false/writable=false; optional verifier-checkpoint readonly meta appended;
infos same six in order then optional verifier-checkpoint then verifier_program.
Instruction program is plan.selected_verifier, data is moved plan.request_bytes.
clear_return_data; invoke; if invoke Err return Err with NO get;
on Ok immediately get_return_data; None/program/length checks; decode; box result and bytes.
These are source observations, NOT yet a native call-log certificate.

RuntimeCpiAccountView is explicit named trust, with exclusion keyed on instruction metas.
Passed-cell contents after returning CPI remain unconstrained. Borrow-counter/handle stability is not supplied by this row.
RuntimeReturnData/RuntimeReturnDataClear are separate explicit hypotheses.
RuntimeCpiReadonlyEntry7 remains PENDING and unused.
P1 requires SAME successful far-side emission/program/context and no set/clear/CPI between that emission and read.
The source chronology alone does not instantiate NIB's projected state equality or prove the far-side emission.

PCD_RuntimeRows defines DRAFT typed RowSpec_POOL_344/345 for PCB. Immutable branch inspection found no matching Lean interface at the recorded revision. No PCB theorem is instantiated pending merge. PCD_CpiFrame corrects the PCA candidate exclusion to the instruction meta keys under c-a; it adds no readonly/counter guarantee.
