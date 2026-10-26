import R1Z.PV_CB_EncoderCell
import R1Z.PV_CB_ForwardRange
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_EncoderFill
open Aeneas Aeneas.Std Result ProverRwFull ProverRwSuccessArithmeticTotal
namespace S
abbrev fill {E : Type} := @PV_CB_OwnedEncoder.owned.basis_fill E
abbrev cell {E : Type} := @PV_CB_OwnedEncoder.owned.basis_cell E
end S
def finite {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (width : Usize) (factor : E) :
    Nat → Usize → Array E 512#usize → Result (Array E 512#usize)
  | 0,_,out => .ok out
  | fuel+1,j,out => do
    let out1 ← S.cell inst out width j factor
    finite inst width factor fuel (PV_CB_ForwardRange.advance j) out1

theorem source {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (width : Usize) (factor : E) (fuel : Nat) (j : Usize) (out : Array E 512#usize)
    (rank : j.val+fuel=width.val) :
    S.fill inst out width j factor = finite inst width factor fuel j out := by
  unfold S.fill
  induction fuel generalizing j out with
  | zero =>
    have done : ¬j<width := by change ¬j.val<width.val;omega
    rw [PV_CB_OwnedEncoder.owned.basis_fill]
    simp only [done,if_false,finite]
  | succ fuel ih =>
    have more : j<width := by change j.val<width.val;omega
    have advance := PV_CB_ForwardRange.advance_val j width more
    rw [PV_CB_OwnedEncoder.owned.basis_fill]
    simp only [more,if_true,lift,bind_tc_ok,finite]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hnext
    exact ih (PV_CB_ForwardRange.advance j) next (by omega)
theorem finite_total {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (mul_total : ∀ a b,Total (inst.mul a b))
    (width : Usize) (factor : E) (fuel : Nat) (j : Usize) (out : Array E 512#usize)
    (rank : j.val+fuel=width.val) (half : 2*width.val≤512) :
    Total (finite inst width factor fuel j out) := by
  induction fuel generalizing j out with
  | zero => exact ok_total _
  | succ fuel ih =>
    have more : j.val<width.val := by omega
    simp only [finite]
    apply bind_total (PV_CB_EncoderCell.total inst mul_total out width j factor half more)
    intro next
    exact ih (PV_CB_ForwardRange.advance j) next
      (by rw [PV_CB_ForwardRange.advance_val j width more];omega)
theorem total {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (mul_total : ∀ a b,Total (inst.mul a b))
    (width : Usize) (factor : E) (out : Array E 512#usize) (half : 2*width.val≤512) :
    Total (S.fill inst out width 0#usize factor) := by
  rw [source inst width factor width.val 0#usize out (by simp)]
  exact finite_total inst mul_total width factor width.val 0#usize out (by simp) half
#print axioms source
#print axioms finite_total
#print axioms total
end R1Z.PV_CB_EncoderFill
