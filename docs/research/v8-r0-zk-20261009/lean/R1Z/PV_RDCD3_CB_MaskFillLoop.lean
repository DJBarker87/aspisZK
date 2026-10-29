import R1Z.PV_RDCD3_CB_MaskFillBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_MaskFillLoop
open Aeneas Aeneas.Std Result ControlFlow PV_RDCD3_CB_ForwardRange PV_RDCD3_CB_MaskCell

theorem c1_run (data : Array Q 16#usize) (iter : Range) (coeff : Coeff) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0 iter data coeff =
      PV_RDCD3_CB_ForwardLoop.run (cell data PV_RDCD3_CB_MaskIndices.S.factors) iter.start iter.end coeff := by
  rcases iter with ⟨i,stop⟩
  unfold PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0 PV_RDCD3_CB_ForwardLoop.run
  apply congrArg (fun body : Range × Coeff → Result (ControlFlow (Range × Coeff) Coeff) =>
    loop body (between i stop,coeff))
  funext pair
  rcases pair with ⟨r,c⟩
  exact PV_RDCD3_CB_MaskFillBody.c1 data r c
theorem mask_run (data : Array Q 10#usize) (iter : Range) (coeff : Coeff) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1 iter data coeff =
      PV_RDCD3_CB_ForwardLoop.run (cell data PV_RDCD3_CB_MaskIndices.S.maskFactors) iter.start iter.end coeff := by
  rcases iter with ⟨i,stop⟩
  unfold PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1 PV_RDCD3_CB_ForwardLoop.run
  apply congrArg (fun body : Range × Coeff → Result (ControlFlow (Range × Coeff) Coeff) =>
    loop body (between i stop,coeff))
  funext pair
  rcases pair with ⟨r,c⟩
  exact PV_RDCD3_CB_MaskFillBody.mask data r c
theorem c1_finite (data : Array Q 16#usize) (fuel : Nat) (i stop : Usize) (coeff : Coeff)
    (rank : i.val+fuel=stop.val) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0 (between i stop) data coeff =
      PV_RDCD3_CB_ForwardLoop.finite (cell data PV_RDCD3_CB_MaskIndices.S.factors) fuel i coeff := by
  exact (c1_run data (between i stop) coeff).trans
    (PV_RDCD3_CB_ForwardLoop.source _ fuel i stop coeff rank)
theorem mask_finite (data : Array Q 10#usize) (fuel : Nat) (i stop : Usize) (coeff : Coeff)
    (rank : i.val+fuel=stop.val) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1 (between i stop) data coeff =
      PV_RDCD3_CB_ForwardLoop.finite (cell data PV_RDCD3_CB_MaskIndices.S.maskFactors) fuel i coeff := by
  exact (mask_run data (between i stop) coeff).trans
    (PV_RDCD3_CB_ForwardLoop.source _ fuel i stop coeff rank)
#print axioms c1_run
#print axioms mask_run
#print axioms c1_finite
#print axioms mask_finite
end R1Z.PV_RDCD3_CB_MaskFillLoop
