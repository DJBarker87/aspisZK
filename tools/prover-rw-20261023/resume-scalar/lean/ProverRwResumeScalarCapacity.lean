import ProverRwResumeScalarCoordinate

/- Matches the actual literal-assignment count branches, not a source refinement. -/
namespace ProverRwResumeScalar

def nextCount (count : Nat) : Nat :=
  match count with | 0 => 1 | 1 => 2 | 2 => 3 | n => n

theorem normal_record_bound (count : Nat) (h : count < 3) :
    nextCount count = count + 1 ∧ nextCount count ≤ 3 := by
  match count with
  | 0 => constructor <;> (first | rfl | omega)
  | 1 => constructor <;> (first | rfl | omega)
  | 2 => constructor <;> (first | rfl | omega)
  | n + 3 => omega

theorem saturated_no_arithmetic (count : Nat) (h : 3 ≤ count) :
    nextCount count = count := by
  match count with
  | 0 | 1 | 2 => omega
  | n + 3 => rfl

theorem normal_three_capacity :
    nextCount 0 = 1 ∧ nextCount (nextCount 0) = 2 ∧
    nextCount (nextCount (nextCount 0)) = 3 := by
  exact ⟨rfl, rfl, rfl⟩

theorem entry_increment (entry : Nat) (h : entry < 16) :
    entry + 1 ≤ 16 ∧ entry + 1 < 2^64 ∧
    (entry + 1 < 16 ↔ entry < 15) := by omega

#print axioms normal_record_bound
#print axioms saturated_no_arithmetic
#print axioms normal_three_capacity
#print axioms entry_increment
end ProverRwResumeScalar
