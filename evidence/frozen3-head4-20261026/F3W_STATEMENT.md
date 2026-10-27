# Stage 1: exact target and quantifiers

Branch codex/cx-frozen3-head4-20261026. Only F3W_ modules and this receipt
directory may change. Budget: 100 actual single-module Lean attempts, 0 Kani.
No headline or non-vacuity construction is in scope.

Inherited accepted raw interface, written before proving:

    retained owners/trust/history/L159 ->
    forall s : F3T_ByteCarrier.Submission, forall H : Bytes -> State,
      (eval H (F3T_Installed.source c hashv (input c s))).2 = true ->
      eval H (F3T_Installed.source c hashv (input c s)) =
        eval H (F3_Model.verifier D (input c s))
      OR chargedCollision H (SAME complete account experiment).

Here c = F3V_Install.configuration base; equality includes the complete
ordered oracle log with duplicates and the acceptance result, under the SAME H.
No fixed native SHA realization of every H, independent accepted execution,
prepared success, model acceptance or log equality may enter as a premise.
Owner leaves must be instantiated on the derived submission witnesses.

The requested rejected-branch argument is stronger than the inherited
F3U_CollisionJoin.Join definition: that definition is acceptance guarded.
A clarification of this difference has been requested while source proofs
continue. A rejected-branch argument must distinguish verdict equality from
full log equality; two rejecting programs need not have the same oracle log.
No unguarded statement is silently substituted for the inherited interface.

Read: root AGENTS (Security and proof discipline), supplied common/local rules,
S2 ownership/plan/diagnosis, C3-BIN route B and owner amendment, S2LeadInterface,
SInt2 handoff, F3V handoff, and F3U/F3T/F3S dependencies. The design paths in
the task are under docs/research/100bit-spend-path-20261013/.

Validation plan: smallest new module first in the coherent SInt2 host cache,
existing unchanged S2W runners, -j1 -M7000, one own capped scope, 6G high / 8G
max / swap 0 / TasksMax64. Receipts retain source revision/hash, direct object
fingerprints, command, status, wall, peak RSS, swaps and all printed axioms.
No package replay or shipped-source changes; inherited ELF pins are not
freshly reproduced by this proof-only job.
