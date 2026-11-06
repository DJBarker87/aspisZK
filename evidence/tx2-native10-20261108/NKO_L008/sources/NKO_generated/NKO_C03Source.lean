import NKO_C03Core
set_option autoImplicit false
noncomputable section
namespace NKO_C03
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Every actual inactive event uses the selected current proof bytes.
The preceding checked slice must return before this event exists. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_EventAll.Holds (Holds proof)
  (run wr rr merkle finish d pub proof ck hash none) := by
 unfold run
 simp only [NHT_Constants.compact.OFF_INACTIVE,NHT_Constants.compact.OFF_ROUND0,
  NKE_Entered.lift_ok]
 repeat' first
 | nke_zeta
 | nko_c03_bind
 | nke_intro
 | nke_lift
 | nke_pure
 | nko_c03_record
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
#print axioms source
end NKO_C03
