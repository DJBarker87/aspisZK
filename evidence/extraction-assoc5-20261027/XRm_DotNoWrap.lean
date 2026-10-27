import XRm_DotBounds
open Aeneas Aeneas.Std Result
open XRk_Release XRm_DotBounds
namespace XRm_DotNoWrap
def natStep (j : Fin 4) (s : Nat) (v : XRl_DotSums.Operand) := s+term j v

/-- A bounded history accumulates ordinary natural sums. No no-wrap premise
is assumed; the per-term bound follows from the actual four raw cells. -/
theorem fold (j : Fin 4) (ops : List XRl_DotSums.Operand) (n : Nat) (start : U64)
    (budget : n+ops.length≤4096) (initial : start.val≤n*B) :
    (ops.foldl (XRl_DotSums.cellStep j) start).val=ops.foldl (natStep j) start.val ∧
    (ops.foldl (XRl_DotSums.cellStep j) start).val≤(n+ops.length)*B := by
  induction ops generalizing n start with
  | nil =>
    constructor
    · rfl
    · simpa only [List.foldl_nil,List.length_nil,Nat.add_zero] using initial
  | cons v rest ih =>
    have ht := term_bound j v
    have safe : start.val+term j v<18446744073709551616 := by
      simp only [List.length_cons] at budget
      unfold B at *
      omega
    have nextBound : (XRl_DotSums.cellStep j start v).val≤(n+1)*B := by
      rw [step_value j start v safe]
      unfold B at *
      omega
    have tail := ih (n+1) (XRl_DotSums.cellStep j start v) (by
      simp only [List.length_cons] at budget
      omega) nextBound
    constructor
    · simp only [List.foldl_cons]
      rw [tail.1,step_value j start v safe]
      rfl
    · simpa only [List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail.2

theorem zero (j : Fin 4) (ops : List XRl_DotSums.Operand) (bound : ops.length≤4096) :
    (ops.foldl (XRl_DotSums.cellStep j) 0#u64).val=ops.foldl (natStep j) 0 ∧
    (ops.foldl (XRl_DotSums.cellStep j) 0#u64).val<18446744073709551616 := by
  have h := fold j ops 0 0#u64 (by omega) (by simp)
  refine ⟨h.1,?_⟩
  have hv := h.2
  unfold B at hv
  omega

theorem operands_length (xs : List XRl_DotHistory.Input)
    (ops : List (fast_pairing.canonical.Q × fast_pairing.canonical.Q × fast_pairing.canonical.Q))
    (history : XRl_DotSums.Operands xs ops) : ops.length=xs.length := by
  induction history with
  | nil => rfl
  | append prior v a b q converts ih =>
    simp only [List.length_append,List.length_singleton]
    omega
#print axioms fold
#print axioms zero
#print axioms operands_length
end XRm_DotNoWrap
