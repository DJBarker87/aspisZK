import R1Z.ProverCommitShippedSchedule

/-! Exhaustiveness of the first-acceptance partition used by the direct
shipped-scalar Kani harness. No execution transport is inferred from this
arithmetic lemma; concrete receipts must separately check each branch. -/
set_option autoImplicit false
namespace R1Z.ProverCommitScalarPartition

/-- A bounded candidate sequence either first accepts at `stop < n`, with
all preceding candidates equal to the rejection value, or exhausts at n. -/
theorem first_accept_partition (n p : Nat) (c : Nat → Nat)
    (bounded : ∀ i, i < n → c i ≤ p) :
    ∃ stop, stop ≤ n ∧ (∀ i, i < stop → c i = p) ∧
      (stop < n → c stop < p) := by
  induction n generalizing c with
  | zero => exact ⟨0, by omega, by omega, by omega⟩
  | succ n ih =>
    by_cases accept : c 0 < p
    · exact ⟨0, by omega, by omega, fun _ => accept⟩
    · have rejected : c 0 = p := by have := bounded 0 (by omega); omega
      obtain ⟨stop, hstop, hprefix, hnext⟩ :=
        ih (fun i => c (i + 1)) (fun i hi => bounded (i + 1) (by omega))
      refine ⟨stop + 1, by omega, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact rejected
        | succ i => exact hprefix i (by omega)
      · intro hi
        exact hnext (by omega)

/-- Masking a u32 by 0x7fffffff admits precisely these seventeen cases. -/
theorem sixteen_partition (c : Nat → Nat)
    (bounded : ∀ i, i < 16 → c i ≤ 2147483647) :
    ∃ stop, stop ≤ 16 ∧ (∀ i, i < stop → c i = 2147483647) ∧
      (stop < 16 → c stop < 2147483647) :=
  first_accept_partition 16 2147483647 c bounded

/-- The 31-bit mask supplies the bound, with no candidate-range premise. -/
theorem masked_partition (raw : Nat → Nat) :
    ∃ stop, stop ≤ 16 ∧
      (∀ i, i < stop → raw i &&& 2147483647 = 2147483647) ∧
      (stop < 16 → raw stop &&& 2147483647 < 2147483647) :=
  sixteen_partition (fun i => raw i &&& 2147483647)
    (fun _ _ => Nat.and_le_right)

#print axioms masked_partition
#print axioms first_accept_partition
#print axioms sixteen_partition
end R1Z.ProverCommitScalarPartition
