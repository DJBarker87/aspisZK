import LIBB_ReturnTrace
set_option autoImplicit false
noncomputable section
namespace LIBB_ReturnRun
open Aeneas Aeneas.Std VTop_Stages NJU_CommonObserved LIBB_ReturnTrace
theorem run (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 Safe (NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none) := by
 unfold NJU_CommonObserved.run
 repeat' first
 | apply bind
 | (apply record; intros; intro equal; cases equal)
 | apply lift
 | apply pure
 | intro x
 | split


#print axioms run
end LIBB_ReturnRun
end
