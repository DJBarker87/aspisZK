import VTop_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_ResumeDomain
open Aeneas Aeneas.Std Result VTop_Stages
attribute [local irreducible] verifier.candidate.tx2_common
/-- Parsed and resumed calls share the original proof/public/checkpoint.
The model parser result is explicitly retained, not identified with native. -/
theorem authenticated_of_cuts (ops : VTop_Stages.Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) (pub proof cp : Slice U8)
    (obs : Option (verifier.Phase → Result Unit)) (variant : transport.Variant)
    (parsed : ops.op3 proof = ok (.Ok variant))
    (marked : ops.op13 obs _root_.AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed = ok ())
    (common : verifier.candidate.tx2_common ops D pub proof cp hash obs = ok (.Ok ())) :
    verifier.candidate.tx2_authenticated ops D pub proof cp hash obs = ok (.Ok ()) := by
  simp only [verifier.candidate.tx2_authenticated, parsed,
    core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, marked, common]

/-- next=10 is proved by the top caller's guard on the SAME resumed state,
not imposed as an extra resume precondition. -/
theorem next_ten (ops : VTop_Stages.Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) (pub proof cp : Slice U8)
    (obs : Option (verifier.Phase → Result Unit)) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (split : ops.op16 = ok 10#usize)
    (resumed : ops.op18 D cp proof pub .S2 hash = ok (.Ok (p,a)))
    (accepted : verifier.candidate.tx2_common ops D pub proof cp hash obs = ok (.Ok ())) :
    a.next = 10#usize := by
  unfold verifier.candidate.tx2_common at accepted
  simp only [resumed, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, split] at accepted
  head_reduce accepted
  split at accepted
  · cases accepted
  · rename_i same
    simpa only [bne_iff_ne, not_not] using same
#print axioms authenticated_of_cuts
#print axioms next_ten
end AspisR1.NCK_ResumeDomain
end
