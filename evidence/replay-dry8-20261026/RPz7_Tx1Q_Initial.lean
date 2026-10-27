import RPz7_Tx1Q_QueryBridge
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Initial
open AspisR1Stage2 Port2_Initial

/-- Factor the existing constructor proof without its unused VTop dictionary
argument. This is the same concrete constructor, not a new initial-state port. -/
theorem raw (reserved : Bool) (a : verifier.Accumulator)
    (accepted : Port3_Initial.constructor reserved .S2 = ok (.Ok a)) :
    reserved = true ∧ a.weights.val = List.replicate 64 zeroK ∧
      a.rhs = zeroE ∧ a.power = oneK ∧ a.next = 0#usize := by
  rw [Port3_Initial.constructor_shell] at accepted
  obtain ⟨weights,success,eq⟩ := (newS2_success _ a).mp accepted
  obtain ⟨reservedEq,contents⟩ := CheckpointBytes3Allocation.filled_success_content
    reserved 64#usize zeroK weights success
  subst a
  exact ⟨reservedEq,contents,rfl,rfl,rfl⟩

theorem fields (reserved : Bool) (a : verifier.Accumulator)
    (accepted : Port3_Initial.constructor reserved .S2 = ok (.Ok a)) :
    a.weights.val.length = 64 ∧ a.next.val = 0 ∧
    Port3_FlushInstall.Canonical a.power ∧ Port4C_QueryArithmetic.CanonE a.rhs ∧
    CheckpointBytes5Output.accumulator a = QueryAccumulator.initial := by
  obtain ⟨_,weights,rhs,power,next⟩ := raw reserved a accepted
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [weights,List.length_replicate]
  · rw [next]; rfl
  · rw [power]
    change (1#u32).val<2147483647 ∧ (0#u32).val<2147483647 ∧
      (0#u32).val<2147483647 ∧ (0#u32).val<2147483647
    decide
  · rw [rhs]
    change ((0#u32).val<2147483647 ∧ (0#u32).val<2147483647 ∧
      (0#u32).val<2147483647 ∧ (0#u32).val<2147483647) ∧
      ((0#u32).val<2147483647 ∧ (0#u32).val<2147483647 ∧
      (0#u32).val<2147483647 ∧ (0#u32).val<2147483647)
    decide
  · unfold CheckpointBytes5Output.accumulator QueryAccumulator.initial
    congr 1
    · funext j
      simp only [weights,List.getElem?_replicate,if_pos j.isLt,Option.getD_some,
        Port3_Constants.decode_zero_k]
    · rw [rhs,Port3_Constants.decode_zero_e]
    · rw [power,Port3_Constants.decode_one_k]
    · rw [next]; rfl

#print axioms raw
#print axioms fields
end AspisR1.Tx1Q_Initial
end
