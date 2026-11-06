import NLR_PrepareDenote
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_constructor  (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.constructor logical v sem⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_constructor cfg i logical v sem) := by
 simp only [step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_constructor]
 try rfl
#print axioms run_constructor
end AspisR1.NLR_Prepare
end
