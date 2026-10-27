import LPt_LPl_C_ChunkFrame
import LPt_LPl_A_ScanCongruence
set_option autoImplicit false
namespace LPt_LPl_C.Echeck
/-- Induction transports the checked one-chunk tail law to every loop length.
This is a model theorem: native Slice/heap association is still separate. -/
theorem append_tail (xs tail : List Aeneas.Std.U8) (k : Bool) (n : Nat)
    (size : xs.length = 32*n) (small : tail.length < 32) :
    LPt_LPl_A.Echeck.loop (xs++tail) k = LPt_LPl_A.Echeck.loop xs k := by
  apply LPt_LPl_A.echeck_stage_congruence
  · simp only [List.length_append, size]
    omega
  · intro i hi
    have contained : 32*i+32 ≤ xs.length := by
      have bound : i+1 ≤ n := by
        simp only [List.length_append, size] at hi
        omega
      have mul := Nat.mul_le_mul_left 32 bound
      omega
    unfold LPt_LPl_A.Echeck.predicate
    rw [LPt_LPl_C.window_append xs tail (32*i) 32 contained]
#print axioms append_tail
end LPt_LPl_C.Echeck
