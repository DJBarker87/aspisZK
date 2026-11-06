import NLR_PrepareDenote
import NLJ_RunAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_valueRange  (cfg : Configuration) {H : Type} (i : Input H) (n offY1 : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.valueRange n offY1 semantic y1 splitBack vecBack⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_valueRange cfg i n offY1 semantic y1 splitBack vecBack) := by
 simp only [Bind.bind,Pure.pure,step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_valueRange]
 repeat' first
 | (solve | rfl)
 | (solve | contradiction)
 | (apply NLJ_RunAlgebra.bind_congr; intro)
 | split
#print axioms run_valueRange
end AspisR1.NLR_Prepare
end
