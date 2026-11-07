import NMC_HeapLaws
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Exit
open Aeneas Aeneas.Std Result NMC_Parent
/-- The SAME live Box is released only on a returning Err path. Runtime
cleanup may itself abort; Result then contains no fictitious after-heap. -/
def cleanup {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (heap : Heap) (identity : Nat) : Result (A×Heap) := do
 let after ← allocator.cleanup state
 ok (after,write heap identity none)
theorem cleanup_frame {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (heap : Heap) (identity address : Nat) (disjoint : address≠identity) :
 (do let after ← cleanup allocator state heap identity
     ok (after.1,after.2 address))=
 (do let after ← allocator.cleanup state
     ok (after,heap address)) := by
 unfold cleanup
 cases h : allocator.cleanup state with
 | fail error=>rfl
 | div=>rfl
 | ok after=>simp only [bind_tc_ok,write_frame heap identity address none disjoint]
theorem cleanup_abort {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (heap : Heap) (identity : Nat) (error : Error)
 (aborted : allocator.cleanup state=fail error) :
 cleanup allocator state heap identity=fail error := by simp only [cleanup,aborted,bind_tc_fail]
/-- Error mapping executes before Box cleanup. There is no cleanup on an
outer nonreturning child, and no successful child premise is introduced. -/
def public {A E T : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (heap : Heap) (identity : Nat) (reply : Result (core.result.Result T E)) :
 Result (core.result.Result T AspisR1PublicPreparation.r1_wire.Error×A×Heap) := do
 let result ← reply
 match result with
 | .Ok value=>ok (.Ok value,state,heap)
 | .Err _=>do
   let after ← cleanup allocator state heap identity
   ok (.Err .Public,after.1,after.2)
theorem public_abort {A E T : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (heap : Heap) (identity : Nat) (error : Error) :
 public (E:=E) (T:=T) allocator state heap identity (fail error)=fail error := rfl
#print axioms cleanup_frame
#print axioms cleanup_abort
#print axioms public_abort
end AspisR1.NMC_Exit
end
