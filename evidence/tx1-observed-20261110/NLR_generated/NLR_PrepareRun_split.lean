import NLR_PrepareDenote
import NLJ_RunAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_split  (cfg : Configuration) {H : Type} (i : Input H) (n : Usize) (logical : alloc.vec.Vec U8) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.split n logical⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_split cfg i n logical) := by
 simp only [Bind.bind,Pure.pure,step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_split]
 repeat' first
 | (solve | rfl)
 | (apply NLJ_RunAlgebra.bind_congr; intro)
 | split
#print axioms run_split
end AspisR1.NLR_Prepare
end
