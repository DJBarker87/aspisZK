import NJR_Cuts
set_option autoImplicit false
namespace NJR_ReaderCut
open Aeneas Aeneas.Std
abbrev K := VTop_Stages.aspis_core.field.QM31
abbrev Error := VTop_Stages.verifier.Error

/-- Payload transcription of NJR_parent::reader_backing K007--010. SAME
backing is an immutable slice equality, justified by native pointer+length and
arbitrary byte assertions. Ownership metadata and the actual Vec drop are
native observations, not a law derived from a pointer. -/
def Cut (bytes observed : Slice U8) (before : List K) (i : Nat)
 (reply : core.result.Result K Error) (readerPost : Nat)
 (result : core.result.Result (List K × Nat) Error) (freed : Bool) : Prop :=
 observed=bytes ∧
 match reply with
 | .Err e => result=.Err e ∧ freed=true
 | .Ok q => result=.Ok (before.set i q,readerPost) ∧ freed=false

/-- On the error prefix the owned vector does not escape; no suffix/store or
successful output is assumed. Success keeps the SAME vector and exact frame. -/
theorem error_prefix (bytes observed : Slice U8) (before : List K) (i : Nat)
 (e : Error) (post : Nat) (result : core.result.Result (List K × Nat) Error)
 (freed : Bool) (cut : Cut bytes observed before i (.Err e) post result freed) :
 observed=bytes ∧ result=.Err e ∧ freed=true :=
 ⟨cut.1,cut.2⟩

/-- Each entered native step's arbitrary byte observation has a full immutable
backing frame. This is why the child domain applies to the parent's Reader. -/
theorem backing (bytes observed : Slice U8) (before : List K) (i : Nat)
 (reply : core.result.Result K Error) (post : Nat)
 (result : core.result.Result (List K × Nat) Error) (freed : Bool)
 (cut : Cut bytes observed before i reply post result freed) (j : Nat) :
 observed.val[j]?=bytes.val[j]? := by rw [cut.1]

#print axioms error_prefix
#print axioms backing
end NJR_ReaderCut
