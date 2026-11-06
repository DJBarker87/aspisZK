import NLR_PrepareDenote
import NLJ_RunAlgebra
import NLJ_CodeRight
import NLJ_PrepareWindow_constructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem run_constructor  (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.constructor logical v sem⟩) (continuation cfg)) =
 run (NLR_PrepareTails.tail_constructor cfg i logical v sem) := by
 rw [step_constructor cfg ⟨i,.constructor logical v sem⟩ logical v sem rfl]
 unfold window_constructor NLR_PrepareTails.tail_constructor
 simp only [Bind.bind,Pure.pure,NLJ_Monad.bind_assoc]
 generalize hclosed : BorrowedClaimPrepared.closedPreparationCode i.digest sem v i.hash i.scratch = closed
 have terminal := NLJ_RunAlgebra.inl_return (B := State H) closed (continuation cfg (H := H)) (fun out => rfl)
 rw [NLJ_Monad.bind_assoc] at terminal
 exact terminal
#print axioms run_constructor
end AspisR1.NLR_Prepare
end
