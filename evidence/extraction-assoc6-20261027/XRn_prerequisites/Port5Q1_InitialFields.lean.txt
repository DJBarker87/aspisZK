import Port3_Initial
import Port4C_QueryArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_InitialFields
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem accepted (base : VTop_Stages.Ops) (reserved : Bool) (a : verifier.Accumulator)
    (run : Port3_Initial.constructor reserved .S2=ok (.Ok a)) :
    a.weights.val.length=64 ∧ a.next.val=0 ∧ Port3_FlushInstall.Canonical a.power ∧
      Port4C_QueryArithmetic.CanonE a.rhs ∧
      CheckpointBytes5Output.accumulator a=QueryAccumulator.initial := by
  have fields := Port3_Initial.accepted_fields base reserved a run
  refine ⟨?_,?_,?_,?_,Port3_Initial.accepted_initial base reserved a run⟩
  · rw [fields.2.1,List.length_replicate]
  · rw [fields.2.2.2.2]; rfl
  · rw [fields.2.2.2.1]
    change (1#u32).val<2147483647 ∧ (0#u32).val<2147483647 ∧
      (0#u32).val<2147483647 ∧ (0#u32).val<2147483647
    decide
  · rw [fields.2.2.1]
    change ((0#u32).val<2147483647 ∧ (0#u32).val<2147483647 ∧
      (0#u32).val<2147483647 ∧ (0#u32).val<2147483647) ∧
      ((0#u32).val<2147483647 ∧ (0#u32).val<2147483647 ∧
      (0#u32).val<2147483647 ∧ (0#u32).val<2147483647)
    decide

#print axioms accepted
end AspisR1.Port5Q1_InitialFields
end
