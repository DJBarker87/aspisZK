import NLJ_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem run_mark0 {H : Type} (i : Input H) (p : r1_wire.Prefix) :
 run (PreparedHashCode.bind (step {input:=i,locals:=.mark0 p}) continuation) =
 run (denote {input:=i,locals:=.mark0 p}) := by
 rfl
#print axioms run_mark0
end AspisR1.NLJ_Observed
end
