import NMX_ObserveResult
import NKY_BoxAction
set_option autoImplicit false
noncomputable section
namespace NMX_BoxProjection
open Aeneas Aeneas.Std Result AdapterRw NMX_Carrier
open AspisR1
/-- Project complete Box outcomes. Owners remain present in the native reply;
the canonical view only erases the pure allocator post-state. -/
def observe {A B S : Type} (f : A → B) :
 Result (core.result.Result (NKY_BoxAction.Owned A) solana_program_error.ProgramError × S) →
 RSL.Obs (Except RSL.ProgramError B)
 | .ok (.Ok box,_) => ⟨.ret (.ok (f box.value)),[]⟩
 | .ok (.Err e,_) => ⟨.ret (.error (error e)),[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩

theorem rejected {A B S : Type} (f : A → B)
 (allocator : S2W_D189Wrappers.Allocator S) (before : S) (size : Nat)
 (reservation : NP6_StdModel.Reservation) (owner : Nat)
 (e : solana_program_error.ProgramError) :
 observe f (NKY_BoxAction.run allocator before size reservation owner (.ok (.Err e))) =
 ⟨.ret (.error (error e)),[]⟩ := rfl

theorem allocated {A B S : Type} (f : A → B)
 (allocator : S2W_D189Wrappers.Allocator S) (before post : S) (size owner : Nat)
 (value : A) (allocation : allocator.allocate before size = .ok post) :
 observe f (NKY_BoxAction.run allocator before size (.Ok ()) owner (.ok (.Ok value))) =
 ⟨.ret (.ok (f value)),[]⟩ := by
 rw [NKY_BoxAction.returning allocator before post size owner value allocation]
 rfl

theorem stopped {A B S : Type} (f : A → B)
 (allocator : S2W_D189Wrappers.Allocator S) (before : S) (size owner : Nat)
 (reservation : NP6_StdModel.Reservation) (value : A) (e : Error)
 (allocation : allocator.allocate before size = .fail e) :
 observe f (NKY_BoxAction.run allocator before size reservation owner (.ok (.Ok value))) =
 ⟨.abort,[]⟩ := by
 rw [NKY_BoxAction.allocator_failure allocator before size reservation owner value e allocation]
 rfl
#print axioms rejected
#print axioms allocated
#print axioms stopped
end NMX_BoxProjection
end
