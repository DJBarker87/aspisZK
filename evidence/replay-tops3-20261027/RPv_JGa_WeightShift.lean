import RPv_JFy_Steps
set_option autoImplicit false
namespace AspisR1.JGa_WeightShift
open Aeneas Aeneas.Std Result WP

def bit (i : U64) : U32 := UScalar.cast .U32 (i &&& 1#u64)
theorem bound (i : U64) : (bit i).val≤1 := by
  have hv : (i &&& 1#u64).val≤1 := by rw [UScalar.val_and];exact Nat.and_le_right
  unfold bit
  scalar_tac
#print axioms bound

theorem shift (index : U64) (level : U8) (hl : level.val<64) : ∃ out,index>>>level=ok out := by
  obtain ⟨out,call,_⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec index level hl)
  exact ⟨out,call⟩
#print axioms shift
end AspisR1.JGa_WeightShift
