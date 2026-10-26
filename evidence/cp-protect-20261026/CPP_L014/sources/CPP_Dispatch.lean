import CPP_OracleSource
import Hiq_DispatchRelease
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Dispatch
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation
open Hiq_DispatchSource
attribute [local instance] Classical.propDecidable

/-- Preserve outer failure/divergence and the exact inner ProgramError. -/
def eraseValue {T : Type} : Result (core.result.Result T Hiq_DispatchSource.PE) → Result (core.result.Result Unit Hiq_DispatchSource.PE)
  | .fail e => .fail e
  | .div => .div
  | .ok (.Err e) => .ok (.Err e)
  | .ok (.Ok _) => .ok (.Ok ())

def reply {A : Type} : Reply A → Result (core.result.Result Unit Hiq_DispatchSource.PE)
  | .inl r => eraseValue r
  | .inr r => eraseValue r

def callbacks {A Account : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (store : Store) (call : Call A)
    (lifecycle : Key → Slice Account → Slice U8 → Result (core.result.Result Unit Hiq_DispatchSource.PE)) : Ops Account where
  first := fun id accounts data => eraseValue
    (CPP_Invocation.first n1 copy allocator id store ⟨{call with data := data},accounts.val.length⟩)
  second := fun id accounts data => eraseValue
    (CPP_Invocation.second n2 allocator id store ⟨{call with data := data},accounts.val.length⟩)
  init := lifecycle
  write := lifecycle
  finalize := lifecycle

/-- Actual extracted release dispatcher instantiated with guarded complete
wrapper interpretations. Lifecycle implementations are arbitrary and absent
from the result; the original account slice/count and instruction are retained. -/
theorem source {A Account : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (call : Call A)
    (accounts : Slice Account)
    (lifecycle : Key → Slice Account → Slice U8 → Result (core.result.Result Unit Hiq_DispatchSource.PE)) :
    process_r1_cost_probe_instruction (callbacks n1 n2 copy allocator store call lifecycle) id accounts call.data =
      reply (CPP_Invocation.native n1 n2 copy allocator id store ⟨call,accounts.val.length⟩).2.2 := by
  rw [Hiq_DispatchRelease.source]
  cases route : Hiq_ReleaseRoute.route call.data with
  | reject => rfl
  | second => rfl
  | first =>
    simp only [CPP_Invocation.native,route,callbacks,reply]
    cases CPP_Invocation.first n1 copy allocator id store (⟨call,accounts.val.length⟩ : Invocation A) with
    | fail e => rfl
    | div => rfl
    | ok result => cases result <;> rfl

#print axioms source
end AspisR1.CPP_Dispatch
end
