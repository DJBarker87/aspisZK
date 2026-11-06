import NLR_PrepareDenote
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_mapSemantic  (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) (r : core.result.Result (r1_semantic.Verified H) r1_wire.Error) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.mapSemantic logical v r⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_mapSemantic cfg i logical v r) := by
 simp only [step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,
  NLR_PrepareTails.tail_mapSemantic]
 try rfl
#print axioms run_mapSemantic
end AspisR1.NLR_Prepare
end
