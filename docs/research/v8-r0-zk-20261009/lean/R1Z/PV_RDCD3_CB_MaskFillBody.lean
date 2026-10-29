import R1Z.PV_RDCD3_CB_MaskCell
import R1Z.PV_RDCD3_CB_ForwardLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_MaskFillBody
open Aeneas Aeneas.Std Result ControlFlow PV_RDCD3_CB_ForwardRange PV_RDCD3_CB_MaskCell

def reply {N : Usize} (data : Array Q N) (exponents : Array U8 N)
    (response : Result (Option Usize × Range)) (coeff : Coeff) :
    Result (ControlFlow (Range × Coeff) Coeff) := do
  let (column,iter1) ← response
  match column with
  | none => .ok (.done coeff)
  | some column => do
    let out ← cell data exponents column coeff
    .ok (.cont (iter1,out))

theorem c1_reply (data : Array Q 16#usize) (iter : Range) (coeff : Coeff) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0.body data iter coeff =
      reply data PV_RDCD3_CB_MaskIndices.S.factors (next iter) coeff := by
  simp only [PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0.body,
    reply,cell,Aeneas.Std.uncurry,bind_assoc_eq,next,PV_RDCD3_CB_MaskIndices.S.factors,PV_RDCD3_CB_MaskIndices.S.maskFactors]
  all_goals rfl
theorem mask_reply (data : Array Q 10#usize) (iter : Range) (coeff : Coeff) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1.body data iter coeff =
      reply data PV_RDCD3_CB_MaskIndices.S.maskFactors (next iter) coeff := by
  simp only [PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1.body,
    reply,cell,Aeneas.Std.uncurry,bind_assoc_eq,next,PV_RDCD3_CB_MaskIndices.S.factors,PV_RDCD3_CB_MaskIndices.S.maskFactors]
  all_goals rfl
theorem c1 (data : Array Q 16#usize) (iter : Range) (coeff : Coeff) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0.body data iter coeff =
      PV_RDCD3_CB_ForwardLoop.body (cell data PV_RDCD3_CB_MaskIndices.S.factors) iter coeff := by
  rw [c1_reply]
  rcases iter with ⟨i,stop⟩
  by_cases more : i<stop
  · trans reply data PV_RDCD3_CB_MaskIndices.S.factors (.ok (some i,between (advance i) stop)) coeff
    · exact congrArg (fun response => reply data PV_RDCD3_CB_MaskIndices.S.factors response coeff) (next_step i stop more)
    · simp only [reply,bind_tc_ok,Aeneas.Std.uncurry,PV_RDCD3_CB_ForwardLoop.body,between,more,if_true]
  · trans reply data PV_RDCD3_CB_MaskIndices.S.factors (.ok (none,between i stop)) coeff
    · exact congrArg (fun response => reply data PV_RDCD3_CB_MaskIndices.S.factors response coeff) (next_done i stop (by change ¬i.val<stop.val at more;omega))
    · simp only [reply,bind_tc_ok,Aeneas.Std.uncurry,PV_RDCD3_CB_ForwardLoop.body,between,more,if_false]
theorem mask (data : Array Q 10#usize) (iter : Range) (coeff : Coeff) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1.body data iter coeff =
      PV_RDCD3_CB_ForwardLoop.body (cell data PV_RDCD3_CB_MaskIndices.S.maskFactors) iter coeff := by
  rw [mask_reply]
  rcases iter with ⟨i,stop⟩
  by_cases more : i<stop
  · trans reply data PV_RDCD3_CB_MaskIndices.S.maskFactors (.ok (some i,between (advance i) stop)) coeff
    · exact congrArg (fun response => reply data PV_RDCD3_CB_MaskIndices.S.maskFactors response coeff) (next_step i stop more)
    · simp only [reply,bind_tc_ok,Aeneas.Std.uncurry,PV_RDCD3_CB_ForwardLoop.body,between,more,if_true]
  · trans reply data PV_RDCD3_CB_MaskIndices.S.maskFactors (.ok (none,between i stop)) coeff
    · exact congrArg (fun response => reply data PV_RDCD3_CB_MaskIndices.S.maskFactors response coeff) (next_done i stop (by change ¬i.val<stop.val at more;omega))
    · simp only [reply,bind_tc_ok,Aeneas.Std.uncurry,PV_RDCD3_CB_ForwardLoop.body,between,more,if_false]
#print axioms c1_reply
#print axioms mask_reply
#print axioms c1
#print axioms mask
end R1Z.PV_RDCD3_CB_MaskFillBody
