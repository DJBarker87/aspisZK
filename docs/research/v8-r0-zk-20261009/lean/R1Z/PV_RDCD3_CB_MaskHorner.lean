import R1Z.PV_RDCD3_CB_MaskLinearsFinite
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_MaskHorner
open Aeneas Aeneas.Std Result ControlFlow PV_RDCD3_ReverseRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize
abbrev Prepared := PV_RDCD3_CB_PreparedTotal.Prepared
namespace S
abbrev loop := PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop2
abbrev body := PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop2.body
abbrev add := PV_RDCD3_FieldSource.aspis_core.field.QM31.add
abbrev mul := PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.mul
end S
def finite (coeff : Coeff) (p : Prepared) : Nat → Usize → Q → Result Q
  | 0,_,shared => .ok shared
  | fuel+1,e,shared => do
    let product ← S.mul p shared
    let q ← Array.index_usize coeff (pred e)
    let next ← S.add product q
    finite coeff p fuel (pred e) next
set_option backward.isDefEq.respectTransparency false in
theorem source (coeff : Coeff) (p : Prepared) (fuel : Nat) (e : Usize) (shared : Q)
    (rank : e.val=fuel) : S.loop (before e) coeff p shared = finite coeff p fuel e shared := by
  unfold S.loop PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop2
  induction fuel generalizing e shared with
  | zero =>
    have zero : e=0#usize := UScalar.eq_of_val_eq rank
    subst e
    rw [PV_RDCD3_LoopUnfold.loop_bind]
    simp only [PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop2.body,
      next_zero,bind_tc_ok,finite]
    try rfl
  | succ fuel ih =>
    have step := next_pos e (by omega)
    unfold next at step
    rw [PV_RDCD3_LoopUnfold.loop_bind]
    simp only [PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop2.body,
      step,bind_tc_ok,finite]
    try dsimp only [Aeneas.Std.uncurry]
    simp only [bind_assoc_eq,bind_tc_ok]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro value hvalue)
    exact ih (pred e) _ (by rw [pred_val];omega)
#print axioms source
end R1Z.PV_RDCD3_CB_MaskHorner
