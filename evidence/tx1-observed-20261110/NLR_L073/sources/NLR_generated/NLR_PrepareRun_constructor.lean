import NLR_PrepareDenote
import NLJ_RunAlgebra
import NLJ_CodeRight
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_constructor  (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.constructor logical v sem⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_constructor cfg i logical v sem) := by
 change run (AspisR1PublicPreparation.PreparedHashCode.bind
  (AspisR1PublicPreparation.PreparedHashCode.bind
   (BorrowedClaimPrepared.closedPreparationCode i.digest sem v i.hash i.scratch)
   (fun out => Code.done (Sum.inl out : Post H))) (continuation cfg)) =
 run (AspisR1PublicPreparation.PreparedHashCode.bind
  (BorrowedClaimPrepared.closedPreparationCode i.digest sem v i.hash i.scratch) Code.done)
 rw [NLJ_CodeRight.right]
 apply NLJ_RunAlgebra.inl_return
 intro out
 rfl
#print axioms run_constructor
end AspisR1.NLR_Prepare
end
