import NLJ_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem run_mark1 {H : Type} (i : Input H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges) :
 run (PreparedHashCode.bind (step {input:=i,locals:=.mark1 p t c}) continuation) =
 run (denote {input:=i,locals:=.mark1 p t c}) := by
 rfl
#print axioms run_mark1
end AspisR1.NLJ_Observed
end
