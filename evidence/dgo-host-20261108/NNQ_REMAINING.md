Target not yet established. Stop reason: the ONLY authorized budget, 30 Lean
scopes, is exhausted (16 pass,14 rejected). This is not Kani exhaustion.
All remaining work is Lean-only; it needs no Kani or extraction allowance.

Item8 OPEN: prove the two dictionary equalities at GExq_FirstCode.code and
GExq_SecondCode.code for arbitrary shared-carrier dictionaries (and hence for
AspisS6CurrentFirstInstallation.toDigest D1/D2). The exact typed proposed
statements are in NNQ_FirstCode.lean.txt, explicitly UNCOMPILED. Use the new
DSim preparation law through SdkD_PrepareLower.lower and the compiled
batch_eq/batch_stage_eq. No child result or acceptance premise is authorized.
The proposal's import NNQ_Batch must be changed to NNQ_COMBINED_IMPORT, where
item7 actually lives. Item8 was written but no scope remained to attempt it
before the required final combined import. No claim it is impossible.

Item9 OPEN: for arbitrary Configuration c, o, hashv, A and x y : S2W_Trace.Call A,
CallSim x y must imply equality between GExq_ChildCode.execute at the fields of
withDigest c o on x and at c on y (use AuS1_Install.base c.stageBase as the stage
field). Same-call cases exclude op43 by NotDigest; op10/op11 consume item8.
No item9 statement/proof was compiled. It depends on item8, not on Kani.

Item10 OPEN: account_withDigest must prove
  ART_PartialAccount.account (withDigest c o) hashv copy allocator id a =
  ART_PartialAccount.account c hashv copy allocator id a
for arbitrary c/o/hashv/copy/allocator/id/adversary, retaining all error and
divergence prefixes and adaptive choices. Compose sdk_withDigest, the two
outer-stage Sim laws, lowerN_sim and item9 through the installed wrappers.
Then prove recorder independence using observe_op43 and split, yielding EXACTLY
AspisR1.DGP_HostDigest.O2 with ONLY its existing three premises. No account or
recorder theorem was compiled; no new trust or restricted adversary is proposed.

NNH_ consumer remains NNH_RecordedCharge.bound transported by O1 and O2.
O1's archive correction was noted in NNH_'s handoff but NOT recompiled here.
Condition(4)'s owner-approved pointwise-inclusion strategy is RECORDED, NOT
proved. Actual-run inclusion, the same probability space and exact charged
event association remain the integration job's obligations. This job closes
no NDT row and proves no part of the deployed headline bound.

No real host counterexample to O2 was found. Host differences encountered:
coherent RPz7 import owner, a preserved observer Result step, and the nominal
RPz7_PhaseIso.Phase observer type. None issues Call.op43 or branches on its
reply. Mirror leaky_differs still identifies that forbidden trace as the
load-bearing counterexample shape; absence in completed components does not
replace the unproved items8-10.

No permission request, cap/timeout increase, new premise, source/trust/model
edit or stopped sibling scope. The numerical target remains unchanged.

Continuation: item8 CLOSED by NNQ_L031 (firstCode_eq, secondCode_eq); items9-10 remain OPEN. New budget used1/20. Runner budget guard updated to count only L031 onward, keeping all admission/cap checks.

target not yet established

Continuation: item9 CLOSED by child_sim, NNQ_L032; arbitrary Configuration, hashv and CallSim calls. Stage field is AuS1_Install.base c.stageBase. New budget used2/20. Item10 OPEN.

target not yet established
