import GExq_InstalledWrapper
import GExp_CountLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_WrapperBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open CheckpointBytes5Effect GExp_CountLaws

theorem first {A : Type} (body : Code S2W_Observation.Answer) (n : Nat)
    (bounded : count n body)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (state : A) :
    count n (GExq_WrapperCode.first body copy allocator e state) := by
  unfold GExq_WrapperCode.first
  apply lift_bind_count
  intro allocated
  apply then_count (Nat.le_refl n) bounded
  intro result
  cases result with
  | Err error => exact pure_count _ _
  | Ok saved =>
    split
    · exact lift_count _ _
    · apply lift_bind_count
      intro cleaned
      exact pure_count _ _

theorem second {A : Type}
    (body : Code (core.result.Result Unit AdapterRw.Cuts.PE)) (n : Nat)
    (bounded : count n body) (allocator : Allocator A) (e : Entry) (state : A) :
    count n (GExq_WrapperCode.second body allocator e state) := by
  unfold GExq_WrapperCode.second
  apply lift_bind_count
  intro allocated
  apply then_count (Nat.le_refl n) bounded
  intro result
  cases result with
  | Err error => exact pure_count _ _
  | Ok value =>
    cases value
    apply lift_bind_count
    intro cleaned
    exact pure_count _ _

#print axioms first
#print axioms second
end AspisR1.RPx_WrapperBudget
end
