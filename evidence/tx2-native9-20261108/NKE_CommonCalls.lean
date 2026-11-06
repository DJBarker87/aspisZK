import NKE_CommonCallsTactic
set_option autoImplicit false
noncomputable section
namespace NKE_CommonCalls
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- No external endpoint/log premise: every source event uses its actual args. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_EventAll.Holds (Clause wr rr merkle finish d hash)
  (run wr rr merkle finish d pub proof ck hash none) := by
 unfold run
 repeat' first
 | nke_zeta
 | nke_bind
 | nke_intro
 | nke_lift
 | nke_pure
 | nke_calls_record
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
#print axioms source
end NKE_CommonCalls
