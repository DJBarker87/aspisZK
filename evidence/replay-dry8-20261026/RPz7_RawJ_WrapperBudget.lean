import RPz7_RawJ_ChildBudget
import RPz7_GExq_WrapperCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_WrapperBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open CheckpointBytes5Effect GExp_CountLaws
local instance : MonadLift Result Code where monadLift := liftResult

theorem first {A : Type} (body : Code S2W_Observation.Answer) (n : Nat) (bound : count n body)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (state : A) :
    count n (GExq_WrapperCode.first body copy allocator e state) := by
  unfold GExq_WrapperCode.first
  apply lift_bind_count; intro allocated
  apply then_count (p:=body) (cost:=n)
  · omega
  · exact bound
  · intro result
    cases result with
    | Err error => exact pure_count _ _
    | Ok saved =>
      dsimp only
      cases copied : copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive)
          (e.heap.accounts 2).1 (S2W_CommittedCheckpoint.source (S2W_ReturnedCheckpoint.nativeBytes saved)) with
      | panic => simp only [copied]; exact lift_count _ _
      | returned written =>
        simp only [copied]
        apply lift_bind_count; intro cleaned; exact pure_count _ _

theorem second {A : Type} (body : Code (core.result.Result Unit AdapterRw.Cuts.PE))
    (n : Nat) (bound : count n body) (allocator : Allocator A) (e : Entry) (state : A) :
    count n (GExq_WrapperCode.second body allocator e state) := by
  unfold GExq_WrapperCode.second
  apply lift_bind_count; intro allocated
  apply then_count (p:=body) (cost:=n)
  · omega
  · exact bound
  · intro result
    cases result with
    | Err error => exact pure_count _ _
    | Ok u => cases u; apply lift_bind_count; intro cleaned; exact pure_count _ _

#print axioms first
#print axioms second
end AspisR1.RawJ_WrapperBudget
end
