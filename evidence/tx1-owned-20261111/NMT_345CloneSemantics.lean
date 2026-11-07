import NMT_RSL_Base
set_option autoImplicit false
namespace NMT_345CloneSemantics
open RSL
/-- Proposed correction under the EXISTING std/allocator semantics. The only
allocating ProgramError variant is the nonempty String; no generic may-abort
arm is added. This is a model/transcription item, not a native row root. -/
def cloneError (e : ProgramError) : RS ProgramError :=
 match e with
 | .borshIoError msg =>
   if msg.isEmpty then RS.pure e
   else RS.seq (RS.lift Spec.alloc) (RS.pure e)
 | _ => RS.pure e

def SnapshotError (e : ProgramError) : Prop :=
 e = .accountBorrowFailed ∨ e = .invalidAccountData

theorem snapshot_clone (e : ProgramError) (safe : SnapshotError e) :
 cloneError e = RS.pure e := by
 rcases safe with rfl | rfl <;> rfl

theorem empty_string_clone : cloneError (.borshIoError "") = RS.pure (.borshIoError "") := rfl

theorem string_clone_abort (msg : String) (nonempty : msg.isEmpty = false) (env : Env) :
 cloneError (.borshIoError msg) env ⟨.abort,[]⟩ := by
 have stopped : RS.seq (RS.lift Spec.alloc) (RS.pure (ProgramError.borshIoError msg)) env ⟨.abort,[]⟩ :=
  Or.inr (Or.inl ⟨[],Or.inr (Or.inl ⟨[],Or.inr rfl,rfl⟩),rfl⟩)
 simpa only [cloneError,nonempty,Bool.false_eq_true,if_false] using stopped

#print axioms snapshot_clone
#print axioms empty_string_clone
#print axioms string_clone_abort
end NMT_345CloneSemantics
