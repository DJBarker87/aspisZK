import R1Z.PV_CB_OwnedEncoder
import R1Z.ProverRwP6ArrayRead
import R1Z.ProverRwSuccessPointsTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_EncoderCell
open Aeneas Aeneas.Std Result ProverRwFull ProverRwSuccessArithmeticTotal
namespace S
abbrev cell {E : Type} := @PV_CB_OwnedEncoder.owned.basis_cell E
end S

theorem read_bound (width j : Usize) (half : 2*width.val≤512) (inside : j.val<width.val) :
    j.val < (512#usize).val := by change j.val<512;omega
theorem write_bound (width j : Usize) (half : 2*width.val≤512) (inside : j.val<width.val) :
    (Usize.wrapping_add width j).val < (512#usize).val := by
  rw [Usize.wrapping_add_val_eq]
  change (width.val+j.val)%UScalar.size .Usize < 512
  exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
theorem total {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (mul_total : ∀ a b,Total (inst.mul a b)) (out : Array E 512#usize)
    (width j : Usize) (factor : E) (half : 2*width.val≤512) (inside : j.val<width.val) :
    Total (S.cell inst out width j factor) := by
  unfold S.cell PV_CB_OwnedEncoder.owned.basis_cell
  apply bind_total (ProverRwP6ArrayRead.read out j (read_bound width j half inside));intro value
  apply bind_total (mul_total value factor);intro product
  simp only [lift,bind_tc_ok]
  exact ProverRwSuccessPointsTotal.update_total out _ product (write_bound width j half inside)
#print axioms read_bound
#print axioms write_bound
#print axioms total
end R1Z.PV_CB_EncoderCell
