import NIW_AlignFieldReply
import NIT_CommonChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignCommonExecution
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_CommonChain

def step (w : W) (j : Usize) (before : CommonCells) : Result (CommonCells×Common) := do
 let lhs := kpick (row2 w) (j.val%4)
 let rhs := kpick (row3 w) (j.val/4)
 let reply←FIo_Native.aspis_core.field.QM31.mul lhs rhs
 let after←Array.update before j reply
 ok (after,⟨lhs,rhs,reply,1⟩)

/-- Observe the SAME actual arithmetic call and emitted array update. This is
not a fresh local log selected from the multiplication model. -/
theorem observed (w : W) (hf : NHI_TensorOuterStep.Factors w)
 (j : Usize) (small : j.val<16) (before : CommonCells) (hc : NHI_CellCanon.array before) :
 NIW_AlignFieldReply.Produced (step w j before) (fun result=>
  cutCommon (row2 w) (row3 w) j.val before result.2 result.1 ∧
  QMul result.2.lhs result.2.rhs result.2.reply ∧ NHI_CellCanon.array result.1) := by
 let lhs := kpick (row2 w) (j.val%4)
 let rhs := kpick (row3 w) (j.val/4)
 have cl := NIT_CommonInterpretation.kpick_canonical (row2 w) (hf 0 (by decide) 2 (by decide)) _ (by change j.val%4<4;omega)
 have cr := NIT_CommonInterpretation.kpick_canonical (row3 w) (hf 0 (by decide) 3 (by decide)) _ (by change j.val/4<4;omega)
 have actual := NIW_AlignFieldReply.qm lhs rhs cl cr
 cases call : FIo_Native.aspis_core.field.QM31.mul lhs rhs with
 | fail err => simp only [NIW_AlignFieldReply.Produced,call] at actual
 | div => simp only [NIW_AlignFieldReply.Produced,call] at actual
 | ok reply =>
  change QMul lhs rhs reply ∧ canonQ reply at actual
  have update := NIT_LowInterpretation.update_model before j reply small
  have frame : ∀ k,k<16 → kpick (NIT_ArrayFrames.put before j.val reply) k=
   if k=j.val then reply else kpick before k := by
   intro k hk
   exact NIT_ArrayFrames.pick_put FIo_Native.aspis_core.field.QM31.ZERO before j.val reply small k
  unfold step
  change FIo_Native.aspis_core.field.QM31.mul
   (kpick (row2 w) (j.val%4)) (kpick (row3 w) (j.val/4))=ok reply at call
  rw [call,bind_tc_ok,update,bind_tc_ok]
  exact ⟨⟨small,rfl,rfl,rfl,frame⟩,actual.1,
   NHM_ArrayPreserve.canonical canonQ before _ j reply hc actual.2 update⟩

#print axioms observed
end AspisR1.NIW_AlignCommonExecution
