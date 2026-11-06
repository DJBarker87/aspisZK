import NLR_PrepareDenote
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_view  (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.view logical semantic y1⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_view cfg i logical semantic y1) := by
 simp only [step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_view]
 try rfl
#print axioms run_view
end AspisR1.NLR_Prepare
end
