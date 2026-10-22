import R1Z.ProverCommitBasisFillValue47
/-! Finite forward native counter sequences, kept symbolic even at 1024 cells. -/
set_option autoImplicit false
namespace R1Z.ProverCommitCounterList48
open Aeneas Aeneas.Std

def counters : Nat → Usize → List Usize
 | 0,_ => []
 | n+1,i => i::counters n (Usize.wrapping_add i 1#usize)

theorem increment (i : Usize) (hi : i.val < 1024) :
    (Usize.wrapping_add i 1#usize).val=i.val+1 := by
  rw [ProverCommitBasisFillValue47.add_val i 1#usize (by change i.val+1 < 2048;omega)]
  rfl

theorem bounds (n : Nat) (i : Usize) (bound : i.val+n ≤ 1024) :
    ∀ k ∈ counters n i, i.val ≤ k.val ∧ k.val < i.val+n := by
  induction n generalizing i with
  | zero => simp only [counters,List.not_mem_nil,false_implies,implies_true]
  | succ n ih =>
    intro k hk
    have hi : i.val < 1024 := by omega
    have hv := increment i hi
    simp only [counters,List.mem_cons] at hk
    rcases hk with rfl|hk
    · omega
    · have h := ih (Usize.wrapping_add i 1#usize) (by rw [hv];omega) k hk
      rw [hv] at h
      omega

theorem values (n : Nat) (i : Usize) (bound : i.val+n ≤ 1024) :
    (counters n i).map UScalar.val=List.range' i.val n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have hv := increment i (by omega)
    rw [counters,List.map_cons,ih _ (by rw [hv];omega),hv]
    rfl

#print axioms increment
#print axioms bounds
#print axioms values
end R1Z.ProverCommitCounterList48
