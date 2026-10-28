import R1Z.PV_RDEA_AppendExecution
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_ExecutionHeaders
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_AppendRequests

theorem clone_header {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (base : List U8) (w : World S F)
    (b : Buffer U8) (h : (PV_RDEA_CloneExecution.clone step shape address base w).1=.ok b) :
    b.values=base ∧ b.capacity=base.length := by
  unfold PV_RDEA_CloneExecution.clone at h
  dsimp only at h
  split at h <;> rename_i hr
  · cases h
  · cases h
    exact ⟨rfl,PV_RDEA_CloneExecution.capacity_success step shape address base.length w hr⟩

theorem append_header {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (tail : List U8) (w : World S F)
    (out : Buffer U8) (h : (PV_RDEA_AppendExecution.append step shape b tail w).1=.ok out) :
    out.values=b.values++tail ∧
      out.capacity=nextCapacity b.values.length b.capacity tail.length := by
  unfold PV_RDEA_AppendExecution.append at h
  dsimp only at h
  split at h <;> rename_i hr
  · cases h
  · cases h
    exact ⟨congrArg (fun xs => xs++tail) (PV_RDB1_Append.reserve_values step _ _ shape b tail.length w),
      reserve_success_capacity step _ _ shape b tail.length w hr⟩

#print axioms clone_header
#print axioms append_header
end R1Z.PV_RDEA_ExecutionHeaders
