import NLR_PrepareDenote
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_semantic  (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.semantic logical v⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_semantic cfg i logical v) := by
 simp only [step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_semantic]
 try rfl
#print axioms run_semantic
end AspisR1.NLR_Prepare
end
