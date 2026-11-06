import NLR_PrepareDenote
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_expandSemantic  (cfg : Configuration) {H : Type} (i : Input H) (n offY1 : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.expandSemantic n offY1 semantic y1 compressed splitBack vecBack⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_expandSemantic cfg i n offY1 semantic y1 compressed splitBack vecBack) := by
 simp only [step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_expandSemantic]
 try rfl
#print axioms run_expandSemantic
end AspisR1.NLR_Prepare
end
