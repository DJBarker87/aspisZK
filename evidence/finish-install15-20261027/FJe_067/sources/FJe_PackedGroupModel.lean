import FJe_PackedGroupStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedGroupModel
open Aeneas Aeneas.Std Result
open FIw_ArrayValue (decoded)
open FJb_MatrixGroupStep (State)
open FIv_NativeValue (K)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- The exact actual group reads are the SAME four literal lane positions. -/
theorem input_value (s : State) (g : Fin 4) :
    FJb_MatrixBlock.input s g.val=(fun j=>decoded s (FJe_ExternalAdjoint.lane g j)) := by
  funext j
  have hg := g.isLt
  have hj : j.val<4 := j.isLt
  have hi : 4*g.val+j.val<(16#usize).val := by change 4*g.val+j.val<16;omega
  unfold FJb_MatrixBlock.input
  rw [FJb_MatrixModel.at_value]
  simp only [FJb_MatrixModel.sample,dif_pos hi]
  rfl

theorem value (s : State) : FJe_PackedGroupStep.localModel s=
    FJe_ExternalAdjoint.packedLocal iBasis uBasis (decoded s) := by
  funext g
  exact congrArg (fun f=>R0P.poseidonPackingFormula iBasis uBasis (R0P.poseidonMat4 f))
    (input_value s g)
#print axioms input_value
#print axioms value
end AspisR1.FJe_PackedGroupModel
end
