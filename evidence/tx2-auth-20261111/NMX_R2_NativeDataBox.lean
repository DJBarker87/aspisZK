import NMX_R2_NativeExecution
import NMX_R2_DeferredValue
import NMX_R2_AllocationSound
set_option autoImplicit false
noncomputable section
namespace NMX_R2_NativeDataBox
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_R2_Carrier

def input (a : r1_pool_adapter.owned.OwnedAccount) :
 core.result.Result (Slice U8) solana_program_error.ProgramError :=
 match a.bytes with
 | .Ok value => .Ok value.deref
 | .Err error => .Err error

theorem data_source (env : RSL.Env) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 r1_pool_adapter.owned.OwnedAccount.data (NMX_R2_StdOps.install env aborts failure) a =
 NMX_R2_DeferredValue.run aborts failure (input a) := by
 cases h : a.bytes <;>
  simp only [r1_pool_adapter.owned.OwnedAccount.data,input,h,
   NMX_R2_DeferredValue.run,NMX_R2_StdOps.install]

theorem data (env : RSL.Env) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 RSL.RS.ofCloned (reply (fun v => v.deref) a.bytes) env
  (NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.OwnedAccount.data (NMX_R2_StdOps.install env aborts failure) a)) := by
 rw [data_source]
 have same : reply id (input a) = reply (fun v => v.deref) a.bytes := by
  cases h : a.bytes <;> simp only [input,h,reply,id_eq]
 rw [← same]
 exact NMX_R2_DeferredValue.member aborts failure (input a) env

/-- Allocations are at their named Box sites, after decoder rejection. No
post-stop ownership/heap/cleanup is introduced. -/
theorem box {A : Type} (aborts : Bool) (owner : Nat)
 (decoded : core.result.Result A PE) (env : RSL.Env) :
 NMX_R2_Semantics.boxed owner decoded env (NMX_R2_NativeExecution.box aborts owner decoded) := by
 cases decoded with
 | Err e => rfl
 | Ok value =>
   cases aborts with
   | false => exact NMX_R2_AllocationSound.returned (Box.mk owner value) env
   | true => exact NMX_R2_AllocationSound.aborted (Box.mk owner value) env
#print axioms data_source
#print axioms data
#print axioms box
end NMX_R2_NativeDataBox
end
