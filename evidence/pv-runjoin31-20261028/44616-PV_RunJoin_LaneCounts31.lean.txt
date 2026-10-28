import R1Z.PV_RunJoin_LaneFold31
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LaneCounts31
open Aeneas Aeneas.Std Result

theorem count (n : Fin 20) :
    UScalar.cast .U32 (Usize.ofNatCore n.val (by have := n.isLt; simp; omega)) =
      U32.ofNatCore n.val (by have := n.isLt; simp; omega) := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  simp only [Usize.ofNatCore_val_eq,U32.ofNatCore_val_eq]
  exact Nat.mod_eq_of_lt (by have := n.isLt; simp; omega)
#print axioms count

theorem shift (index : U32) (n : Fin 20) :
    U32.wrapping_shr index (UScalar.cast .U32
      (Usize.ofNatCore n.val (by have := n.isLt; simp; omega))) =
      U32.wrapping_shr index (U32.ofNatCore n.val (by have := n.isLt; simp; omega)) :=
  congrArg (U32.wrapping_shr index) (count n)
#print axioms shift
end R1Z.PV_RunJoin_LaneCounts31
