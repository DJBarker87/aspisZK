import NLR_PrepareDenote
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_allocate  (cfg : Configuration) {H : Type} (i : Input H)  :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.allocate ⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_allocate cfg i ) := by
 simp only [step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_allocate]
 try rfl
#print axioms run_allocate
end AspisR1.NLR_Prepare
end
