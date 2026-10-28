import R1Z.PV_CB_OwnedEncoder
import R1Z.PV_DL_EncoderRange
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_EncoderFill
set_option autoImplicit false

def finite {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (width : Usize) (factor : E) : Nat → Usize → Array E 512#usize → Result (Array E 512#usize)
  | 0,_,out => ok out
  | fuel+1,j,out => do
    let out ← PV_CB_OwnedEncoder.owned.basis_cell inst out width j factor
    finite inst width factor fuel (PV_DL_EncoderRange.advance j) out

/-- Finite control transport preserves every Result outcome, with arbitrary
field operations. It does not normalize a chain of field multiplications. -/
theorem source {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (width : Usize) (factor : E) (fuel : Nat) (j : Usize) (out : Array E 512#usize)
    (rank : j.val+fuel=width.val) (size : width.val≤512) :
    PV_CB_OwnedEncoder.owned.basis_fill inst out width j factor=
      finite inst width factor fuel j out := by
  induction fuel generalizing j out with
  | zero =>
    have done : ¬j<width := by change ¬j.val<width.val;omega
    rw [PV_CB_OwnedEncoder.owned.basis_fill]
    simp only [done,if_false,finite]
  | succ fuel ih =>
    have more : j<width := by change j.val<width.val;omega
    have hj : j.val<512 := by omega
    have advance := PV_DL_EncoderRange.advance_val j hj
    rw [PV_CB_OwnedEncoder.owned.basis_fill]
    simp only [more,if_true,lift,bind_tc_ok,finite]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hnext
    exact ih (PV_DL_EncoderRange.advance j) next (by omega)

#print axioms finite
#print axioms source
end R1Z.PV_DL_EncoderFill
