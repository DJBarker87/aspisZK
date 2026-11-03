import R1Z.PV_V263_Family
/-! Reached-domain bounds for the unsuffixed completed counter in the frozen
non-trace helper. Rust type inference must be checked independently; these
lemmas establish that the reached natural count fits a signed 32-bit counter.
No callback success, source type inference or complete worker binding is assumed. -/
set_option autoImplicit false
namespace R1Z.PV_V263_CounterBounds
open PV_RunJoin_WorkRange35
open Aeneas.Std

theorem width_bound (n k : Nat) (bound : n≤14336) : width n k≤896 := by
  unfold width
  split <;> omega

theorem increment_safe (n k completed : Nat) (bound : n≤14336)
    (more : completed<width n k) :
    completed+1≤896 ∧ (completed : Int)+1≤2^31-1 := by
  have h := width_bound n k bound
  constructor <;> omega

theorem sumcheck_count (round : Nat) : 28*2^(9-round)≤14336 := by
  have h : 2^(9-round)≤2^9 := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  exact Nat.mul_le_mul_left 28 h

theorem reached_width (round k : Nat) : width (28*2^(9-round)) k≤896 :=
  width_bound _ k (sumcheck_count round)

theorem commitment_width (k : Nat) : width 27 k≤2 ∧ width 2 k≤1 := by
  simp only [width]
  constructor <;> split <;> omega

theorem actual_count_bound (round : Usize) (valid : round.val<10) :
    (PV_RunJoin_SampleDomain34.count round).val≤14336 := by
  rw [PV_RunJoin_SampleDomain34.count_value round valid,
    PV_RunJoin_SampleDomain34.assignments_value round valid]
  exact sumcheck_count round.val

theorem actual_counter_bound (round : Usize) (valid : round.val<10) (k completed : Nat)
    (more : completed<width (PV_RunJoin_SampleDomain34.count round).val k) :
    completed+1≤896 ∧ (completed : Int)+1≤2^31-1 :=
  increment_safe _ k completed (actual_count_bound round valid) more

#print axioms actual_count_bound
#print axioms actual_counter_bound
#print axioms width_bound
#print axioms increment_safe
#print axioms sumcheck_count
#print axioms reached_width
#print axioms commitment_width
end R1Z.PV_V263_CounterBounds
