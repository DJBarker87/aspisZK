import NLR_PrepareDenote
import NLJ_RunAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_semanticRange  (cfg : Configuration) {H : Type} (i : Input H) (n : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.semanticRange n semantic y1 splitBack vecBack⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_semanticRange cfg i n semantic y1 splitBack vecBack) := by
 simp only [Bind.bind,Pure.pure,step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_semanticRange]
 repeat' first
 | (solve | rfl)
 | (apply NLJ_RunAlgebra.bind_congr; intro)
 | split
#print axioms run_semanticRange
end AspisR1.NLR_Prepare
end
