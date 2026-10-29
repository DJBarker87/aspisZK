import R1Z.PV_RDCD3_CB_OwnedMaskHornerEq
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_V217HornerTotal
open Aeneas Aeneas.Std Result PV_RDCD3_Total PV_RDCD3_ReverseRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize
abbrev Prepared := PV_RDCD3_CB_PreparedTotal.Prepared

set_option backward.isDefEq.respectTransparency false in
theorem finite_total (coeff : Coeff) (p : Prepared) (fuel : Nat) (e : Usize) (s : Q)
    (rank : e.val=fuel) (bounded : e.val≤27) :
    Total (PV_RDCD3_CB_MaskHorner.finite coeff p fuel e s) := by
  induction fuel generalizing e s with
  | zero => exact ok_total s
  | succ fuel ih =>
    have index : (pred e).val<27 := by rw [pred_val];omega
    simp only [PV_RDCD3_CB_MaskHorner.finite]
    apply bind_total (PV_RDCD3_CB_PreparedTotal.mul p s);intro product
    apply bind_total (PV_RDCD3_ArrayRead.read coeff (pred e) index);intro q
    apply bind_total (PV_RDCD3_FieldTotal.q_add product q);intro next
    exact ih (pred e) next (by rw [pred_val];omega) (by rw [pred_val];omega)

set_option backward.isDefEq.respectTransparency false in
theorem source_total (coeff : Coeff) (p : Prepared) (s : Q) :
    Total (PV_RDCD3_CB_MaskHorner.S.loop (before 26#usize) coeff p s) := by
  apply (congrArg PV_RDCD3_Total.Total (PV_RDCD3_CB_MaskHorner.source coeff p 26 26#usize s rfl)).mpr
  exact finite_total coeff p 26 26#usize s rfl (by decide)
#print axioms finite_total
#print axioms source_total
end R1Z.PV_RDCD3_V217HornerTotal
