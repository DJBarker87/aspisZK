import NKE_EventTactic
set_option autoImplicit false
noncomputable section
namespace NKE_CommonSource
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Source clauses at actual occurrences, with no independent endpoint log.
This is a partial window attachment, not a positive TX2:065 theorem. -/
theorem clauses (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_EventAll.Holds (NKE_CommonClauses.Clause rr)
  (run wr rr merkle finish d pub proof ck hash none) := by
 unfold run
 repeat' first
 | nke_zeta
 | nke_bind
 | nke_intro
 | nke_lift
 | nke_pure
 | nke_record
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
#print axioms clauses
end NKE_CommonSource
