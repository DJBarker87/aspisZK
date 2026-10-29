import R1Z.PV_RDCD3_CB_MaskLeaves
import R1Z.PV_RDCD3_ReverseRange
import R1Z.PV_RDCD3_LoopUnfold
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_MaskLinearsFinite
open Aeneas Aeneas.Std Result ControlFlow PV_RDCD3_ReverseRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Points := Array Q 10#usize
namespace S
abbrev loop := PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears_loop
abbrev body := PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears_loop.body
abbrev add := PV_RDCD3_FieldSource.aspis_core.field.QM31.add
end S
def finite (point : Points) : Nat → Usize → Q → Q → Result (Q × Q)
  | 0,_,suffix,weighted => .ok (suffix,weighted)
  | fuel+1,e,suffix,weighted => do
    let coordinate := pred e
    let q ← Array.index_usize point coordinate
    let suffix1 ← S.add suffix q
    let weighted1 ← if coordinate != 0#usize then S.add weighted suffix1 else .ok weighted
    finite point fuel coordinate suffix1 weighted1
set_option backward.isDefEq.respectTransparency false in
theorem source (point : Points) (fuel : Nat) (e : Usize) (suffix weighted : Q)
    (size : e.val=fuel) :
    S.loop (before e) point suffix weighted = finite point fuel e suffix weighted := by
  unfold S.loop PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears_loop
  induction fuel generalizing e suffix weighted with
  | zero =>
    have zero : e=0#usize := UScalar.eq_of_val_eq size
    subst e
    rw [PV_RDCD3_LoopUnfold.loop_bind]
    simp only [PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears_loop.body,
      next_zero,bind_tc_ok,finite]
    rfl
  | succ fuel ih =>
    have step := next_pos e (by omega)
    unfold next at step
    rw [PV_RDCD3_LoopUnfold.loop_bind]
    simp only [PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears_loop.body,
      step,bind_tc_ok,finite]
    try dsimp only [Aeneas.Std.uncurry]
    simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro q hq
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro s hs
    have rank : (pred e).val = fuel := by rw [pred_val];omega
    by_cases zero : pred e = 0#usize
    · have z : (pred e != 0#usize) = false := by simp [zero]
      simp only [z, Bool.false_eq_true, if_false,bind_tc_ok]
      exact ih (pred e) s weighted rank
    · have nz : (pred e != 0#usize) = true := by simp [zero]
      simp only [nz,if_true,bind_assoc_eq,bind_tc_ok]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro w hw
      try simp only [bind_tc_ok]
      exact ih (pred e) s w rank
#print axioms source
end R1Z.PV_RDCD3_CB_MaskLinearsFinite
